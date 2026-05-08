import SystemF.Lc.Norm
import Lean.Elab.Tactic
import Lean.Meta.Tactic.TryThis
import Lean.PrettyPrinter

open Lean Elab Tactic Meta Tactic.TryThis PrettyPrinter

namespace SystemF

namespace LcTactic

def finsetNameType : Expr :=
  mkApp (mkConst ``Finset [levelZero]) (mkConst ``SystemF.Name)

def isFinsetNameType (e : Expr) : Bool :=
  e.isAppOf ``Finset && e.appArg!.isConstOf ``SystemF.Name

def unionMany (xs : Array Expr) : MetaM Expr := do
  if h : xs.size > 0 then
    xs.foldlM (start := 1) (init := xs[0]) fun acc x =>
      mkAppM ``Union.union #[acc, x]
  else
    mkAppOptM ``EmptyCollection.emptyCollection #[some finsetNameType, none]

structure CofiniteRule where
  name : Lean.Name
deriving Inhabited, Repr, BEq

initialize cofiniteExt : SimplePersistentEnvExtension CofiniteRule (Array CofiniteRule) ←
  registerSimplePersistentEnvExtension {
    name := `cofiniteExt
    addEntryFn := fun arr entry => arr.push entry
    addImportedFn := fun arrays => arrays.foldl (init := #[]) fun acc arr => acc ++ arr
  }

initialize registerBuiltinAttribute {
  name := `cofinite
  descr := "Registers a constructor or lemma as a cofinite rule for apply_cofinite"
  add := fun decl _ _ => do
    setEnv <| cofiniteExt.addEntry (← getEnv) { name := decl }
}

structure SupportExtractor where
  -- TODO: unused
  type : Lean.Name
  name  : Lean.Name
deriving Inhabited, Repr, BEq

initialize supportExt : SimplePersistentEnvExtension SupportExtractor (Array SupportExtractor) ←
  registerSimplePersistentEnvExtension {
    name := `supportExt
    addEntryFn := fun arr entry => arr.push entry
    addImportedFn := fun arrays => arrays.foldl (init := #[]) fun acc arr => acc ++ arr
  }

initialize registerBuiltinAttribute {
  name := `cofinite_support
  descr := "Registers a function α → Finset Name for apply_cofinite support collection"
  add := fun decl _ _ => do
    let info ← getConstInfo decl
    let type ← match info.type with
      | .forallE _ domain _ _ =>
        match domain.getAppFn with
        | .const n _ => pure n
        | _ => throwError "cofinite_support: domain of {decl} must be a concrete type"
      | _ => throwError "cofinite_support: {decl} must be a function"
    setEnv <| supportExt.addEntry (← getEnv) { type, name:= decl }
}


def collectSupport : TacticM Expr := withMainContext do
  let mut supports := #[]
  let lctx ← getLCtx
  let env ← getEnv
  let supportFns := supportExt.getState env

  for localDecl in lctx do
    unless (localDecl.isImplementationDetail || localDecl.userName.isInaccessibleUserName) do

      let mut newSupports : Array Expr := #[]

      -- Skip shadowed decls
      let some activeDecl := lctx.findFromUserName? localDecl.userName | continue
      if activeDecl.fvarId != localDecl.fvarId then continue

      let ty ← instantiateMVars localDecl.type

      if (isFinsetNameType ty) then
        newSupports := #[localDecl.toExpr]
      else if (ty.isConstOf ``SystemF.Name) then
        newSupports := #[← mkAppOptM ``Singleton.singleton
            #[some (mkConst ``SystemF.Name), some finsetNameType, none, some localDecl.toExpr]]
      -- else if let .const tyName _ := ty.getAppFn then
       else
        for ext in supportFns do
          -- Disable syntactic check for now
          -- if tyName == ext.type then
            try
              let s ← mkAppM ext.name #[localDecl.toExpr]
              newSupports := newSupports.push s
            catch _ =>
              continue

      for s in newSupports do
        if !supports.contains s then
          supports := supports.push s
  unionMany supports

/- Truncate constructor names for try this. -/
def shortenName (n : Lean.Name) : Lean.Name :=
  match n with
  | .str (.str _ p) s => .mkStr (.mkSimple p) s
  | .str _ s => .mkSimple s
  | _ => n

end LcTactic

syntax (name := apply_cofinite)  "apply_cofinite" : tactic
syntax (name := apply_cofinite_trace) "apply_cofinite?" : tactic

/--
Apply the matching cofinite constructor using support synthesized from
the local context.

The current heuristic is conservative: it unions all visible `Finset Name` locals,
all visible `Name` singletons, and the binder-relevant free-variable sets from visible
syntax locals.
-/
@[tactic apply_cofinite, tactic apply_cofinite_trace]
def evalApplyCofinite : Tactic := fun stx => withMainContext do
  let trace ← match stx with
    | `(tactic| apply_cofinite?) => pure true
    | `(tactic| apply_cofinite) => pure false
    | _ => throwUnsupportedSyntax

  let env ← getEnv
  let rules := LcTactic.cofiniteExt.getState env
  if rules.isEmpty then
    throwError "apply_cofinite: no rules registered. Use @[cofinite] to register constructors."

  let support ← LcTactic.collectSupport
  let mut success := false

  -- a rule is a constructor name
  for rule in rules do
    let state ← saveState
    try
      let supportStx ← delab support
      let ctorIdent := mkIdent rule.name
      let tacStx ← `(tactic| apply $ctorIdent $supportStx)
      evalTactic tacStx
      if trace then
        let ctorIdent := mkIdent <| LcTactic.shortenName rule.name
        let tacStx ← `(tactic| apply $ctorIdent $supportStx)
        addSuggestion stx <| tacStx
      success := true
      break
    catch _ =>
      if trace then
        logInfo m!"apply_cofinite: failed to apply {rule.name}"
      restoreState state
      continue
  if !success then
    throwError "apply_cofinite: no matching cofinite rule found for target {← getMainTarget}."

macro "grind_cofnite" : tactic => `(tactic| apply_cofinite <;> grind)

syntax (name := pick_fresh) "pick_fresh" binderIdent : tactic

/--
Pick a fresh name `x` and add the hypothesis `h : x ∉ L` to the context,
where `L` is a finite set of names synthesized from the local context
using the same heuristic as `apply_cofinite`.
-/
@[tactic pick_fresh]
def evalPickFresh : Tactic := fun stx => withMainContext do
  let (xIdent, hIdent) ← match stx with
  | `(tactic| pick_fresh $x:ident) =>
    let baseName := x.getId.eraseMacroScopes.getString!
    pure (x, mkIdent <| Name.mkSimple s!"h{baseName}")
  | `(tactic| pick_fresh _) => pure ⟨mkIdent `x, mkIdent `hx⟩
  | _ => throwUnsupportedSyntax
  let support ← LcTactic.collectSupport
  let supportStx ← delab support
  -- Add pre fix "h" for hypothesis name
  let tacStx ← `(tactic|
    have ⟨$xIdent, $hIdent⟩ := exists_fresh_name $supportStx;
    try simp only [Finset.mem_union,
      Finset.mem_insert,
      Finset.union_assoc,
      Finset.mem_singleton,
      not_or,
      not_false_eq_true] at $hIdent:ident
  )
  evalTactic tacStx



syntax (name := ln_norm) "ln_norm" : tactic

@[tactic ln_norm]
def evalLnNorm : Tactic := fun stx => withMainContext do
  match stx with
    | `(tactic| ln_norm) => pure
    | _ => throwUnsupportedSyntax

  let tacStx ← `(tactic|
      ( repeat (first
          | apply_cofinite <;> ln_norm
          | intro _
          | simp (discharger := first | grind | aesop) only [ln_norm_simps] at *
        )
        try aesop (rule_sets := [LcRules])
        try grind )
    )
  evalTactic tacStx

end SystemF

import SystemF.Lc.Basic
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

inductive CofiniteKind where
  | lcTyAll
  | lcTmLam
  | lcTmTLam
deriving Inhabited, Repr, BEq

def targetKind? (target : Expr) : MetaM (Option CofiniteKind) := do
  let target ← whnf target
  if target.isAppOf ``SystemF.LcTy then
    let arg ← whnf target.appArg!
    if arg.isAppOf ``SystemF.Ty.all then return some .lcTyAll
  else if target.isAppOf ``SystemF.LcTm then
    let arg ← whnf target.appArg!
    if arg.isAppOf ``SystemF.Tm.lam then return some .lcTmLam
    else if arg.isAppOf ``SystemF.Tm.tLam then return some .lcTmTLam
  return none

def collectSupport (kind : CofiniteKind) : TacticM Expr := withMainContext do
  let mut supports := #[]
  let lctx ← getLCtx
  for localDecl in lctx do
    unless (localDecl.isImplementationDetail || localDecl.userName.isInaccessibleUserName) do

      let mut newSupport? : Option Expr := none

      -- Skip shadowed decls
      let some activeDecl := lctx.findFromUserName? localDecl.userName | continue
      if activeDecl.fvarId != localDecl.fvarId then continue

      let ty ← instantiateMVars localDecl.type

      if (isFinsetNameType ty) then
        newSupport? := localDecl.toExpr
      else if (ty.isConstOf ``SystemF.Name) then
        newSupport? ← mkAppOptM ``Singleton.singleton
            #[some (mkConst ``SystemF.Name), some finsetNameType, none, some localDecl.toExpr]
      else if kind == .lcTyAll && (ty.isConstOf ``SystemF.Ty) then
        newSupport? ← mkAppM ``SystemF.Ty.fv #[localDecl.toExpr]
      else if kind == .lcTmLam && (ty.isConstOf ``SystemF.Tm) then
        newSupport? ← mkAppM ``SystemF.Tm.fv #[localDecl.toExpr]
      else if kind == .lcTmTLam && (ty.isConstOf ``SystemF.Tm) then
        newSupport? ← mkAppM ``SystemF.Tm.fvTy #[localDecl.toExpr]

      if let some newSupport := newSupport? then
        if !supports.contains newSupport then
          supports := supports.push newSupport

  unionMany supports

def constructorName : CofiniteKind → Lean.Name
  | .lcTyAll => ``SystemF.LcTy.all
  | .lcTmLam => ``SystemF.LcTm.lam
  | .lcTmTLam => ``SystemF.LcTm.tLam

def shortConstructorName : CofiniteKind → Lean.Name
  | .lcTyAll => `LcTy.all
  | .lcTmLam => `LcTm.lam
  | .lcTmTLam => `LcTm.tLam

end LcTactic

syntax (name := apply_cofinite)  "apply_cofinite" : tactic
syntax (name := apply_cofinite_trace) "apply_cofinite?" : tactic

/--
Apply the matching cofinite local-closure constructor using support synthesized from
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
  let g ← getMainGoal
  let target ← getMainTarget
  let some kind ← LcTactic.targetKind? target
    | throwError "apply_cofinite: unsupported target {target}"
  let support ← LcTactic.collectSupport kind
  let ctorName := LcTactic.constructorName kind

  if trace then
    let supportStx ← delab support
    let ctorIdent := mkIdent <| LcTactic.shortConstructorName kind
    let tacStx ← `(tactic| apply $ctorIdent $supportStx)
    addSuggestion stx <| tacStx
    logInfo m!"apply_cofinite: applying {ctorName} with support {support}"

  let ctor ← mkAppM ctorName #[support]
  let goals ← g.apply ctor
  replaceMainGoal goals

macro "grind_cofnite" : tactic => `(tactic| apply_cofinite <;> grind)

end SystemF

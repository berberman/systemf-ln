import SystemF.Syntax

namespace SystemF

inductive TyConcrete where
  | var (x : Name)
  | arr (T₁ T₂ : TyConcrete)
  | all (x : Name) (T : TyConcrete)
deriving Repr, DecidableEq

inductive TmConcrete where
  | var (x : Name)
  | app (t₁ t₂ : TmConcrete)
  | tApp (t : TmConcrete) (T : TyConcrete)
  | lam (x : Name) (T : TyConcrete) (t : TmConcrete)
  | tLam (T : Name) (t : TmConcrete)
deriving Repr, DecidableEq

def TyConcrete.elab (ctx : List Name) : TyConcrete → Ty
  | .var x => match ctx.findIdx? (· == x) with
    | some idx => #T idx
    | none => $T x
  | .arr T₁ T₂ => (T₁.elab ctx) ⇒ (T₂.elab ctx)
  | .all x T => ∀' (T.elab (x :: ctx))

def TmConcrete.elab (ctxTy ctxTm : List Name) : TmConcrete → Tm
  | .var x => match ctxTm.findIdx? (· == x) with
    | some idx => #v idx
    | none => $v x
  | .app t₁ t₂ => (t₁.elab ctxTy ctxTm) ◦ (t₂.elab ctxTy ctxTm)
  | .tApp t T => (t.elab ctxTy ctxTm)⦃(T.elab ctxTy)⦄
  | .lam x T t => ƛ (T.elab ctxTy) => (t.elab ctxTy (x :: ctxTm))
  | .tLam T t => Λ' t.elab (T :: ctxTy) ctxTm


example : TmConcrete.elab [] [] (.tLam "T" (.lam "x" (.var "T") (.var "x"))) =
    (Λ'(ƛ #T0 => #v0)) := by rfl

end SystemF

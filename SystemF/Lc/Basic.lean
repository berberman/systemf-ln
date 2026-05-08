import SystemF.Subst.TyTm
import SystemF.Lc.Tactic

namespace SystemF

open Notation

/-- A type `T` is locally closed if its bound indices are properly bound.
  Here we use cofinite quantification.
-/
inductive LcTy : Ty → Prop where
  | fvar x : LcTy ($T x)
  | arr T₁ T₂ : LcTy T₁ → LcTy T₂ → LcTy (T₁ ⇒ T₂)
  | all (L : Finset Name) T : (∀ X ∉ L, LcTy (T⟪$T X⟫)) → LcTy (∀' T)

/-
  Similar to `LcTy`, but for terms.
-/
inductive LcTm : Tm → Prop where
  | fvar x : LcTm ($v x)
  | app t₁ t₂ : LcTm t₁ → LcTm t₂ → LcTm (t₁ ◦ t₂)
  | lam (L : Finset Name) T t :
      LcTy T → (∀ x ∉ L, LcTm (t⟪$v x⟫)) → LcTm (ƛ T => t)
  | tApp t T : LcTm t → LcTy T → LcTm (t⦃T⦄)
  | tLam (L : Finset Name) t : (∀ X ∉ L, LcTm (t⟪$T X⟫)) → LcTm (Λ' t)

attribute [cofinite] LcTy.all LcTm.lam LcTm.tLam

attribute [aesop safe apply (rule_sets := [LcRules])]
  LcTy.fvar LcTy.arr
  LcTm.fvar LcTm.app LcTm.tApp

attribute [cofinite_support] Ty.fv Tm.fv Tm.fvTy

attribute [grind =] Finset.mem_union Finset.mem_insert Finset.mem_singleton

end SystemF

import SystemF.Subst.Ty
import SystemF.Subst.Parallel
import SystemF.Lc.Basic

namespace SystemF

open Notation

/-- A simple locally closed type example. -/
example : LcTy (∀' (#T 0 ⇒ #T 0)) := by
  apply_cofinite
  grind [LcTy.fvar, LcTy.arr]

theorem openTy_neq_id {k j : ℕ} {T U V : Ty} (hNeq : k ≠ j) (h : T⟪j, V⟫⟪k, U⟫ = T⟪j, V⟫) :
    T⟪k, U⟫ = T := by
  induction T generalizing k j <;> grind

@[simp]
theorem openTy_lcTy_id {U : Ty} (h : LcTy U) (k : ℕ) (V : Ty) :
    U⟪k, V⟫ = U := by
  induction h generalizing k V with
  | fvar x => grind [LcTy.fvar]
  | arr T₁ T₂ _ _ ih₁ ih₂ => grind [LcTy.arr]
  | all L T _ ih =>
    simp only [openTy_all, Ty.all.injEq]
    pick_fresh X
    grind [openTy_neq_id]

/-- Substitution commutes with opening on types -/
theorem openTy_substTy_comm {k} {X Y : Name} {T U : Ty} (hNeq : X ≠ Y) (hU : LcTy U) :
    (T[X ↦ U])⟪k, ($T Y)⟫ = (T⟪k, $T Y⟫)[X ↦ U] := by
  induction T generalizing k <;> grind [openTy_lcTy_id]

/-- Substitution preserves locally closedness of types -/
theorem substTy_lcTy {T U : Ty} {X : Name} (hT : LcTy T) (hU : LcTy U) : LcTy (T[X ↦ U]) := by
  induction hT with
  | fvar x => grind [LcTy.fvar]
  | arr T₁ T₂ _ _ ih₁ ih₂ => grind [LcTy.arr]
  | all L T _ ih =>
    simp only [subst_all]
    apply_cofinite
    grind [openTy_substTy_comm]

theorem substTy_dist_openTy {T U V : Ty} {X : Name} {k : ℕ} (hU : LcTy U) :
    (T⟪k, V⟫)[X ↦ U] = (T[X ↦ U])⟪k, V[X ↦ U]⟫ := by
  induction T generalizing k <;> grind [openTy_lcTy_id]

/-- If `∀' T` is locally closed (meaning `T` is not closed) and `U` is locally closed,
  then opening `T` with `U` yields a locally closed type.
-/
theorem openTy_lcTy {T U : Ty} (hT : LcTy (∀' T)) (hU : LcTy U) : LcTy (T⟪U⟫) := by
  cases hT with
  | all L T h =>
    pick_fresh X
    specialize h X (by grind)
    have := substTy_lcTy (X := X) h hU
    rw [←substTy_openTy_var (X := X) (by grind)]
    apply this

theorem psubst_openTy_comm' {k} {T U : Ty} {X : Name} {δ : Name → Ty}
    (hX : X ∉ T.fv)
    (hδ : ∀ Y, LcTy (δ Y)) :
    (T.psubst δ)⟪k, U⟫ = (T⟪k, $TX⟫).psubst (Function.update δ X U) := by
  induction T generalizing X k with grind [Ty.psubst, openTy_lcTy_id]

theorem psubst_openTy_comm {k} {T : Ty} {X : Name} {δ : TySubst}
    (hX : X ∉ T.fv)
    (hδ : ∀ Y, LcTy (δ Y)) :
    (T.psubst δ)⟪k, $TX⟫ = (T⟪k, $TX⟫).psubst (Function.update δ X ($T X)) := by
  apply psubst_openTy_comm' hX hδ

lemma psubst_lcTy {T : Ty} (hLc : LcTy T) {δ : TySubst}
    (hδ : ∀ X, LcTy (δ X)) : LcTy (T.psubst δ) := by
  induction hLc generalizing δ with
  | fvar name => exact hδ name
  | arr T₁ T₂ T₁_ih T₂_ih =>
    constructor <;> grind
  | all L T _ ih =>
    apply_cofinite
    grind [psubst_openTy_comm, LcTy.fvar]

def Ty.LcAt (T : Ty) (k : ℕ) : Prop :=
  match T with
  | .bvar idx => idx < k
  | .fvar _ => True
  | .arr T₁ T₂ => T₁.LcAt k ∧ T₂.LcAt k
  | .all T => T.LcAt (k + 1)

theorem lcAtTy_of_openTy {T : Ty} {X : Name} {k : ℕ}
    (h : (T⟪k, $TX⟫).LcAt k) : T.LcAt (k + 1) := by
  induction T generalizing k with grind [Ty.LcAt]

theorem lcAt_zero_of_lcTy {T : Ty} (h : LcTy T) : T.LcAt 0 := by
  induction h with
  | fvar x => simp [Ty.LcAt]
  | arr T₁ T₂ _ _ _ _ => simp [Ty.LcAt] at *; grind
  | all L T _ ih =>
    pick_fresh _
    grind [lcAtTy_of_openTy, Ty.LcAt]

end SystemF

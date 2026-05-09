import SystemF.Subst.Ty
import SystemF.Subst.Parallel
import SystemF.Lc.Basic

namespace SystemF

open Notation

/-- A simple locally closed type example. -/
example : LcTy (∀' (#T 0 ⇒ #T 0)) := by
  apply_cofinite
  grind [LcTy.fvar, LcTy.arr]

theorem Ty.open_neq_id {k j : ℕ} {T U V : Ty} (hNeq : k ≠ j) (h : T⟪j, V⟫⟪k, U⟫ = T⟪j, V⟫) :
    T⟪k, U⟫ = T := by
  induction T generalizing k j <;> grind

@[simp]
theorem Ty.open_lc_id {U : Ty} (h : LcTy U) (k : ℕ) (V : Ty) :
    U⟪k, V⟫ = U := by
  induction h generalizing k V with
  | fvar x => grind [LcTy.fvar]
  | arr T₁ T₂ _ _ ih₁ ih₂ => grind [LcTy.arr]
  | all L T _ ih =>
    simp only [open_all, all.injEq]
    pick_fresh X
    grind [open_neq_id]


/-- Substitution commutes with opening on types -/
@[ln_norm_simps]
theorem Ty.open_subst_comm {k} {X Y : Name} {T U : Ty} (hNeq : X ≠ Y) (hU : LcTy U) :
    (T[X ↦ U])⟪k, ($T Y)⟫ = (T⟪k, $T Y⟫)[X ↦ U] := by
  induction T generalizing k <;> aesop


/-- Substitution preserves locally closedness of types -/
@[aesop safe apply (rule_sets := [LcRules])]
theorem Ty.subst_lc {T U : Ty} {X : Name} (hT : LcTy T) (hU : LcTy U) : LcTy (T[X ↦ U]) := by
  induction hT with
  | fvar x => grind [LcTy.fvar]
  | arr T₁ T₂ _ _ ih₁ ih₂ => grind [LcTy.arr]
  | all L T _ ih =>
    simp only [subst_all]
    apply_cofinite
    intro X hX
    ln_norm


theorem Ty.subst_dist_open {T U V : Ty} {X : Name} {k : ℕ} (hU : LcTy U) :
    (T⟪k, V⟫)[X ↦ U] = (T[X ↦ U])⟪k, V[X ↦ U]⟫ := by
  induction T generalizing k <;> grind [open_lc_id]


/-- If `∀' T` is locally closed (meaning `T` is not closed) and `U` is locally closed,
  then opening `T` with `U` yields a locally closed type.
-/
@[grind ., aesop unsafe 50% apply (rule_sets := [LcRules])]
theorem Ty.open_lc {T U : Ty} (hT : LcTy (∀' T)) (hU : LcTy U) : LcTy (T⟪U⟫) := by
  cases hT with
  | all L T h =>
    pick_fresh X
    specialize h X (by grind)
    have := subst_lc (X := X) h hU
    rw [←subst_open_var (X := X) (by grind)]
    apply this


theorem Ty.psubst_open_comm_update {k} {T U : Ty} {X : Name} {δ : Name → Ty}
    (hX : X ∉ T.fv)
    (hδ : ∀ Y, LcTy (δ Y)) :
    (T.psubst δ)⟪k, U⟫ = (T⟪k, $TX⟫).psubst (Function.update δ X U) := by
  induction T generalizing X k with grind [psubst, open_lc_id]

theorem Ty.psubst_open_comm {k} {T : Ty} {X : Name} {δ : TySubst}
    (hX : X ∉ T.fv)
    (hδ : ∀ Y, LcTy (δ Y)) :
    (T.psubst δ)⟪k, $TX⟫ = (T⟪k, $TX⟫).psubst (Function.update δ X ($T X)) := by
  apply psubst_open_comm_update hX hδ

@[aesop safe apply (rule_sets := [LcRules])]
lemma psubst_lcTy {T : Ty} (hLc : LcTy T) {δ : TySubst}
    (hδ : ∀ X, LcTy (δ X)) : LcTy (T.psubst δ) := by
  induction hLc generalizing δ with
  | fvar name => exact hδ name
  | arr T₁ T₂ T₁_ih T₂_ih =>
    constructor <;> grind
  | all L T _ ih =>
    apply_cofinite
    grind [Ty.psubst_open_comm, LcTy.fvar]

def Ty.LcAt (T : Ty) (k : ℕ) : Prop :=
  match T with
  | .bvar idx => idx < k
  | .fvar _ => True
  | .arr T₁ T₂ => T₁.LcAt k ∧ T₂.LcAt k
  | .all T => T.LcAt (k + 1)

theorem Ty.lcAt_of_open {T : Ty} {X : Name} {k : ℕ}
    (h : (T⟪k, $TX⟫).LcAt k) : T.LcAt (k + 1) := by
  induction T generalizing k with grind [Ty.LcAt]

theorem Ty.lcAt_zero_of_lc {T : Ty} (h : LcTy T) : T.LcAt 0 := by
  induction h with
  | fvar x => simp [LcAt]
  | arr T₁ T₂ _ _ _ _ => grind [LcAt]
  | all L T _ ih =>
    pick_fresh _
    grind [lcAt_of_open, LcAt]

end SystemF

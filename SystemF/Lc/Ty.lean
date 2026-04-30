import SystemF.Subst.Ty

namespace SystemF

open Notation

/-- A type `T` is locally closed if its bound indices are properly bound.
  Here we use cofinite quantification.
-/
@[aesop safe constructors]
inductive LcTy : Ty → Prop where
  | fvar x : LcTy ($T x)
  | arr T₁ T₂ : LcTy T₁ → LcTy T₂ → LcTy (T₁ ⇒ T₂)
  | all (L : Finset Name) T : (∀ X ∉ L, LcTy (T⟪$T X⟫)) → LcTy (∀' T)

/-- A simple locally closed type example. -/
example : LcTy (∀' (#T 0 ⇒ #T 0)) := by
  apply LcTy.all ∅
  aesop

@[aesop safe forward]
theorem openTy_neq_id {k j : ℕ} {T U V : Ty} (hNeq : k ≠ j) (h : T⟪j, V⟫⟪k, U⟫ = T⟪j, V⟫) :
    T⟪k, U⟫ = T := by
  induction T generalizing k j with aesop

@[simp]
theorem openTy_lcTy_id {U : Ty} (h : LcTy U) (k : ℕ) (V : Ty) :
    U⟪k, V⟫ = U := by
  induction h generalizing k V with
  | fvar x => aesop
  | arr T₁ T₂ _ _ ih₁ ih₂ => aesop
  | all L T _ ih =>
    simp only [openTy_all, Ty.all.injEq]
    have ⟨X, hX⟩ := exists_fresh_name L
    have := @ih X hX (k + 1) V
    have := @openTy_neq_id (k + 1) 0 T V ($TX) (by aesop) (by assumption)
    rw [this]
/-- Substitution commutes with opening on types -/
@[aesop unsafe 70% apply]
theorem openTy_substTy_comm {k} {X Y : Name} {T U : Ty} (hNeq : X ≠ Y) (hU : LcTy U) :
    (T[X ↦ U])⟪k, ($T Y)⟫ = (T⟪k, $T Y⟫)[X ↦ U] := by
  induction T generalizing k with aesop

/-- Substitution preserves locally closedness of types -/
@[aesop safe apply]
theorem substTy_lcTy {T U : Ty} {X : Name} (hT : LcTy T) (hU : LcTy U) : LcTy (T[X ↦ U]) := by
  induction hT with
  | fvar x => aesop
  | arr T₁ T₂ _ _ ih₁ ih₂ => aesop
  | all L T _ ih =>
    simp only [subst_all]
    apply LcTy.all (L ∪ {X} ∪ U.fv)
    intro Y hY
    rw [openTy_substTy_comm] <;> aesop

@[aesop unsafe 70% apply]
theorem substTy_dist_openTy {T U V : Ty} {X : Name} {k : ℕ} (hU : LcTy U) :
    (T⟪k, V⟫)[X ↦ U] = (T[X ↦ U])⟪k, V[X ↦ U]⟫ := by
  induction T generalizing k with aesop

/-- If `∀' T` is locally closed (meaning `T` is not closed) and `U` is locally closed,
  then opening `T` with `U` yields a locally closed type.
-/
@[aesop unsafe 50% apply]
theorem openTy_lcTy {T U : Ty} (hT : LcTy (∀' T)) (hU : LcTy U) : LcTy (T⟪U⟫) := by
  cases hT with
  | all L T h =>
    have ⟨X, hX⟩ := exists_fresh_name (L ∪ T.fv)
    specialize h X (by aesop)
    have := substTy_lcTy (X := X) h hU
    rw [←substTy_openTy_var (X := X) (by aesop)]
    apply this




theorem psubst_openTy_comm' {k} {T U : Ty} {X : Name} {δ : Name → Ty}
    (hX : X ∉ T.fv)
    (hδ : ∀ Y, LcTy (δ Y)) :
    (T.psubst δ)⟪k, U⟫ = (T⟪k, $TX⟫).psubst (Function.update δ X U) := by
  induction T generalizing X k with
  | bvar idx =>
    simp [Ty.psubst]
    by_cases idx_eq : idx = k <;> simp [Ty.psubst, idx_eq]
  | fvar Y =>
    have : Y ≠ X := by aesop
    simp only [Ty.psubst, openTy_fvar, ne_eq, this, not_false_eq_true, Function.update_of_ne]
    rw [openTy_lcTy_id]
    apply hδ
  | arr T₁ T₂ T₁_ih T₂_ih =>
    simp [Ty.psubst]
    aesop
  | all T ih =>
    simp only [Ty.psubst, openTy_all, Ty.all.injEq]
    apply ih
    aesop

theorem psubst_openTy_comm {k} {T : Ty} {X : Name} {δ : Name → Ty}
    (hX : X ∉ T.fv)
    (hδ : ∀ Y, LcTy (δ Y)) :
    (T.psubst δ)⟪k, $TX⟫ = (T⟪k, $TX⟫).psubst (Function.update δ X ($T X)) := by
  apply psubst_openTy_comm' hX hδ

lemma psubst_lcTy {T : Ty} (hLc : LcTy T) {δ : Name → Ty}
    (hδ : ∀ X, LcTy (δ X)) : LcTy (T.psubst δ) := by
  induction hLc generalizing δ with
  | fvar name => exact hδ name
  | arr T₁ T₂ T₁_ih T₂_ih =>
    constructor <;> aesop
  | all L T _ ih =>
    apply LcTy.all (L ∪ T.fv)
    intro X hX
    rw [psubst_openTy_comm (by aesop) hδ]
    · apply ih
      · aesop
      · intro Y
        by_cases hY : Y = X
        · aesop
        · aesop


end SystemF

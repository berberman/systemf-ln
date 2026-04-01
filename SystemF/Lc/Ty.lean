import SystemF.Subst.Ty

namespace SystemF


/-
  A type `T` is locally closed if its bound indices are properly bound.
  Here we use cofinite quantification.
  This is equivalent to `LcAtTy 0 T`.
-/
inductive LcTy : Ty → Prop where
  | fvar x : LcTy ($T x)
  | arr T₁ T₂ : LcTy T₁ → LcTy T₂ → LcTy (T₁ ⇒ T₂)
  | all (L : Finset Name) T : (∀ X ∉ L, LcTy (T⟪$T X⟫)) → LcTy (∀' T)

/-
  A simple locally closed type example.
-/
example : LcTy (∀' (#T 0 ⇒ #T 0)) := by
  apply LcTy.all ∅
  intros
  repeat constructor


theorem openTy_neq_id {k j : ℕ} {T U V : Ty} (hNeq : k ≠ j) (h : T⟪j, V⟫⟪k, U⟫ = T⟪j, V⟫) :
    T⟪k, U⟫ = T := by
  induction T generalizing k j with
  | bvar idx =>
    simp at h
    simp
    by_cases idx = j
    · aesop
    · aesop
  | fvar name => simp
  | arr T₁ T₂ T₁_ih T₂_ih =>
    simp
    simp at h
    aesop
  | all T ih =>
    simp at h
    simp only [openTy_all, Ty.all.injEq]
    apply ih (j := j + 1)
    · aesop
    · assumption

@[simp]
theorem openTy_lcTy_id {U : Ty} (h : LcTy U) (k : ℕ) (V : Ty) :
    U⟪k, V⟫ = U := by
  induction h generalizing k V with
  | fvar x => simp
  | arr T₁ T₂ _ _ ih₁ ih₂ =>
    simp only [openTy_arr, Ty.arr.injEq]
    rw [ih₁, ih₂]
    simp
  | all L T _ ih =>
    simp only [openTy_all, Ty.all.injEq]
    have ⟨X, hX⟩ := exists_fresh_name L
    have := @ih X hX (k + 1) V
    have := @openTy_neq_id (k + 1) 0 T V ($TX) (by aesop) (by assumption)
    rw [this]
/-
  Substitution commutes with opening on types
-/
theorem openTy_substTy_comm {k} {X Y : Name} {T U : Ty} (hNeq : X ≠ Y) (hU : LcTy U) :
    (T[X ↦ U])⟪k, ($T Y)⟫ = (T⟪k, $T Y⟫)[X ↦ U] := by
  induction T generalizing k with
  | bvar X =>
    simp only [subst_bvar, openTy_bvar, beq_iff_eq]
    split
    · simp only [subst_fvar, beq_iff_eq, right_eq_ite_iff]
      intro
      contradiction
    · simp
  | fvar Z =>
    simp only [subst_fvar, beq_iff_eq]
    by_cases h : X = Z
    · cases h
      simp only [↓reduceIte]
      have := openTy_lcTy_id hU
      simp [this]
    · simp only [h, ↓reduceIte]
      dsimp [Open.open, openTy]
      simp only [beq_iff_eq, right_eq_ite_iff]
      intro h
      contradiction
  | arr T₁ T₂ T₁_ih T₂_ih =>
    simp only [subst_arr, openTy_arr, Ty.arr.injEq]
    rw [T₁_ih, T₂_ih]
    constructor <;> rfl
  | all T ih =>
    simp only [subst_all, openTy_all, Ty.all.injEq]
    rw [ih]

/-
  Substitution preserves locally closedness of types
-/
theorem substTy_lcTy {T U : Ty} {X : Name} (hT : LcTy T) (hU : LcTy U) : LcTy (T[X ↦ U]) := by
  induction hT with
  | fvar x =>
    simp only [subst_fvar, beq_iff_eq]
    split
    · assumption
    · constructor
  | arr T₁ T₂ _ _ ih₁ ih₂ =>
    constructor
    · apply ih₁
    · apply ih₂
  | all L T _ ih =>
    apply LcTy.all (L ∪ {X} ∪ U.fv)
    intro Y hY
    have h₁ : Y ∉ L := by aesop
    have h₂ : X ≠ Y := by aesop
    change LcTy (T[X ↦ U]⟪$TY⟫)
    rw [openTy_substTy_comm]
    · apply ih
      assumption
    · assumption
    · assumption

theorem substTy_dist_openTy {T U V : Ty} {X : Name} {k : ℕ} (hU : LcTy U) :
    (T⟪k, V⟫)[X ↦ U] = (T[X ↦ U])⟪k, V[X ↦ U]⟫ := by
  induction T generalizing k with
  | bvar idx =>
    simp
    split
    · rfl
    · simp
  | fvar name =>
    simp only [subst_fvar, beq_iff_eq]
    by_cases h : name = X
    · dsimp [Open.open, openTy, Subst.subst, substTy]
      simp only [h, BEq.rfl, ↓reduceIte]
      -- U = openTy k (substTy X U V) U
      change U = (U⟪k, V[X ↦ U]⟫)
      rw [openTy_lcTy_id hU k (V[X ↦ U])]
    · dsimp [Open.open, openTy, Subst.subst, substTy]
      aesop
  | arr T₁ T₂ T₁_ih T₂_ih =>
    simp only [openTy_arr, subst_arr, Ty.arr.injEq]
    rw [T₁_ih, T₂_ih]
    simp_all only [and_self]
  | all T ih =>
    simp only [openTy_all, subst_all, Ty.all.injEq]
    rw [ih]

/-
  If `∀' T` is locally closed (meaning `T` is not closed) and `U` is locally closed,
  then opening `T` with `U` yields a locally closed type.
-/
theorem openTy_lcTy {T U : Ty} (hT : LcTy (∀' T)) (hU : LcTy U) : LcTy (T⟪U⟫) := by
  cases hT with
  | all L T h =>
    have ⟨X, hX⟩ := exists_fresh_name (L ∪ T.fv)
    specialize h X (by aesop)
    have := substTy_lcTy (X := X) h hU
    rw [←substTy_openTy_var (X := X) (by aesop)]
    apply this

end SystemF

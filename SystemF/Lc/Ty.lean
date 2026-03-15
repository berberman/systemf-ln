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
  All bound indices in `T` are strictly less than `k`.
  This is called 'Degree' in A Charguéraud's paper.
-/
inductive LcAtTy : ℕ → Ty → Prop where
  | bvar i k : i < k → LcAtTy k (#T i)
  | fvar X k : LcAtTy k ($T X)
  | arr T₁ T₂ k : LcAtTy k T₁ → LcAtTy k T₂ → LcAtTy k (T₁ ⇒ T₂)
  | all T k : LcAtTy (k + 1) T → LcAtTy k (∀' T)

/-
  A simple locally closed type example.
-/
example : LcTy (∀' (#T 0 ⇒ #T 0)) := by
  apply LcTy.all ∅
  intros
  repeat constructor


/-
  If `T` is locally closed at index `k`, then opening `T` at index `n ≥ k` does nothing.
-/
theorem lcAtTy_openTy_id {T : Ty} {k : ℕ} (h : LcAtTy k T) (n : ℕ) (hn : k ≤ n) (V : Ty) :
    T⟪n, V⟫ = T := by
  induction h generalizing n with
  | bvar i _ _ =>
    have : i ≠ n := by omega
    simp [this]
  | fvar X k =>
    rfl
  | arr _ _ _ _ _ ih₁ ih₂ =>
    simp only [openTy_arr, Ty.arr.injEq]
    rw [ih₁, ih₂]
    constructor
    · rfl
    · rfl
    · assumption
    assumption
  | all T' k h' ih' =>
    simp only [openTy_all, Ty.all.injEq]
    have : k + 1 ≤ n + 1 := by aesop
    rw [ih' (n + 1)]
    assumption

/-
  If opening `T` yields a locally closed type at index `k`,
  then `T` is locally closed at index `k + 1`.
-/
theorem lcAtTy_of_openTy {T : Ty} {X : Name} {k : ℕ}
    (h : LcAtTy k (T⟪k, $TX⟫)) : LcAtTy (k + 1) T := by
  induction T generalizing k with
  | bvar _ =>
    simp only [openTy_bvar, beq_iff_eq] at h
    split at h
    · apply LcAtTy.bvar
      aesop
    · cases h
      apply LcAtTy.bvar
      omega
  | fvar Y =>
    apply LcAtTy.fvar
  | arr T₁ T₂ ih₁ ih₂ =>
    cases h
    apply LcAtTy.arr
    · apply ih₁; assumption
    · apply ih₂; assumption
  | all T' ih' =>
    cases h
    apply LcAtTy.all
    apply ih'
    assumption

/-
  If `T` is locally closed at index `k`, then it is also locally closed at any index `n ≥ k`.
-/
lemma lcAtTy_weaken {T : Ty} {k n : ℕ} (h : LcAtTy k T) (hle : k ≤ n) :
    LcAtTy n T := by
  induction h generalizing n with
  | bvar i k _ => constructor; omega
  | fvar X k => constructor
  | arr T₁ T₂ k _ _ ih₁ ih₂ =>
    constructor
    · apply ih₁; assumption
    · apply ih₂; assumption
  | all T k' _ ih =>
    constructor
    apply ih
    omega

/-
  If `T` is locally closed at index `k + 1` and `U` is locally closed,
  then opening `T` at index `k` with `U` yields a type that is locally closed at index `k`.
-/
lemma lcAtTy_openTy_inv_aux {k : ℕ} {T U : Ty}
  (hT : LcAtTy (k + 1) T) (hU : LcAtTy 0 U) : LcAtTy k (T⟪k, U⟫) := by
  induction T generalizing k with
  | bvar idx =>
    cases hT
    simp only [openTy_bvar, beq_iff_eq]
    by_cases heq : idx = k
    · simp only [heq, ↓reduceIte]
      apply lcAtTy_weaken hU
      omega
    · simp only [heq, ↓reduceIte]
      constructor
      omega
  | fvar name =>
    constructor
  | arr T₁ T₂ T₁_ih T₂_ih =>
    cases hT with
    | arr _ _ _ ih₁ ih₂ =>
      constructor
      · exact T₁_ih ih₁
      · exact T₂_ih ih₂
  | all T ih =>
    cases hT with
    | all _ _ ih' =>
      constructor
      apply ih
      assumption

/-
  If `T` has a bound variable, then opening `T` with a free variable yields a locally closed type.
-/
lemma lcAtTy_openTy_inv {T : Ty} {X : Name} (h : LcAtTy 1 T) : LcAtTy 0 (T⟪$T X⟫) := by
  apply lcAtTy_openTy_inv_aux
  · assumption
  · constructor

/-
  If `T` is locally closed, then `T` is locally closed at index 0
-/
theorem lcTy_implies_lcAtTy0 {T : Ty} (h : LcTy T) : LcAtTy 0 T := by
  induction h with
  | fvar X =>
    apply LcAtTy.fvar
  | arr T₁ T₂ _ _ _ _=>
    apply LcAtTy.arr <;> assumption
  | all L T _ ih =>
    apply LcAtTy.all
    have ⟨X, hX⟩ := exists_fresh_name L
    apply lcAtTy_of_openTy
    exact ih X hX

/-
  If `T` is locally closed at index 0, then `T` is locally closed.
-/
theorem lcAtTy0_implies_lcTy {T : Ty} (h : LcAtTy 0 T) : LcTy T := by
  cases h with
  | bvar i k _ => contradiction
  | fvar X k => constructor
  | arr T₁ T₂ k h₁ h₂ =>
  constructor
  · exact lcAtTy0_implies_lcTy h₁
  · exact lcAtTy0_implies_lcTy h₂
  | all T k h =>
    apply LcTy.all ∅
    intro X hX
    have := lcAtTy_openTy_inv (X := X) h
    exact lcAtTy0_implies_lcTy this
termination_by T.size
decreasing_by
  all_goals (simp_all; dsimp [Ty.size]; omega)

/-
  Locally closed types are exactly those that are locally closed at index 0.
-/
theorem lcTy_iff_lcAtTy0 {T : Ty} : LcTy T ↔ LcAtTy 0 T := by
  constructor
  · apply lcTy_implies_lcAtTy0
  · intro h
    apply lcAtTy0_implies_lcTy h

/-
  If `T` is locally closed, then opening `T` does nothing.
-/
@[simp]
theorem openTy_lcTy_id {U : Ty} (h : LcTy U) (k : ℕ) (V : Ty) :
    U⟪k, V⟫ = U := by
  apply lcAtTy_openTy_id
  · apply lcTy_implies_lcAtTy0 h
  · simp only [zero_le]

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
      dsimp [Open.open, openTy]
      simp
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

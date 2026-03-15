import SystemF.Subst.Class

namespace SystemF


/-
  Open `T` with `U` at index `k`.
-/
def openTy (k : ℕ) (U T : Ty) : Ty :=
  match T with
  | .bvar x => if x == k then U else .bvar x
  | .arr T₁ T₂ => .arr (openTy k U T₁) (openTy k U T₂)
  | .all T => .all (openTy (k + 1) U T)
  | .fvar x => .fvar x

@[simp]
instance : Open Ty Ty where
  «open» := openTy

@[simp]
lemma openTy_bvar {k : ℕ} {U : Ty} {x : ℕ} :
  (#T x)⟪k, U⟫ = if x == k then U else #T x := rfl

@[simp]
lemma openTy0_bvar {U : Ty} {x : ℕ} :
  (#T x)⟪U⟫ = if x == 0 then U else #T x := rfl

@[simp]
lemma openTy_fvar {k : ℕ} {U : Ty} {X : Name} :
  ($T X)⟪k, U⟫ = $T X := rfl

@[simp]
lemma openTy0_fvar {U : Ty} {X : Name} :
  ($T X)⟪U⟫ = $T X := rfl

@[simp]
lemma openTy_arr {k : ℕ} {U T₁ T₂ : Ty} :
  (T₁ ⇒ T₂)⟪k, U⟫ = (T₁⟪k, U⟫ ⇒ T₂⟪k, U⟫) := rfl

@[simp]
lemma openTy0_arr {U T₁ T₂ : Ty} :
  (T₁ ⇒ T₂)⟪U⟫ = (T₁⟪U⟫ ⇒ T₂⟪U⟫) := rfl

@[simp]
lemma openTy_all {k : ℕ} {U T : Ty} :
  (∀' T)⟪k, U⟫ = ∀' (T⟪k + 1, U⟫) := rfl

@[simp]
lemma openTy0_all {U T : Ty} :
  (∀' T)⟪U⟫ = ∀' (T⟪1, U⟫) := rfl


/-
  Substitute free type variable `X` with `U` in `T`
-/
def substTy (X : Name) (U T : Ty) : Ty :=
  match T with
  | .bvar x => Ty.bvar x
  | .fvar Y => if X == Y then U else .fvar Y
  | .arr T₁ T₂ => .arr (substTy X U T₁) (substTy X U T₂)
  | .all T => Ty.all (substTy X U T)

@[simp]
instance : Subst Ty Ty where
  subst := substTy

@[simp] lemma subst_bvar (X : Name) (U : Ty) (x : ℕ) :
  (Ty.bvar x)[X ↦ U] = Ty.bvar x := rfl

@[simp] lemma subst_fvar (X : Name) (U : Ty) (Y : Name) :
  (Ty.fvar Y)[X ↦ U] = if X == Y then U else Ty.fvar Y := rfl

@[simp] lemma subst_arr (X : Name) (U T₁ T₂ : Ty) :
  (Ty.arr T₁ T₂)[X ↦ U] = Ty.arr (T₁[X ↦ U]) (T₂[X ↦ U]) := rfl

@[simp] lemma subst_all (X : Name) (U T : Ty) :
  (Ty.all T)[X ↦ U] = Ty.all (T[X ↦ U]) := rfl

/-
  Opening `T` with free variable `X` and then substituting `X` with `U` is the same as
  opening `T` with `U`, as long as `X` is not free in `T`.
-/
theorem substTy_openTy_var {k} {T U : Ty} {X : Name} (h : X ∉ T.fv) :
    (T⟪k, ($T X)⟫)[X ↦ U] = T⟪k, U⟫ := by
  induction T generalizing k with
  | bvar idx =>
    simp
    by_cases hidx : idx = 0
    · aesop
    · aesop
  | fvar name =>
    dsimp [Open.open, openTy]
    simp only [beq_iff_eq, ite_eq_right_iff]
    by_cases hname : name = X
    · simp [hname]
      simp [Ty.fv] at h
      subst hname
      simp_all only [not_true_eq_false]
    · intro
      simp_all only [not_true_eq_false]
  | arr T₁ T₂ T₁_ih T₂_ih =>
    dsimp [Open.open, openTy]
    simp only [Ty.arr.injEq]
    dsimp [Open.open, openTy] at T₁_ih T₂_ih
    simp only [Ty.fv, Finset.mem_union, not_or] at h
    rw [T₁_ih h.1, T₂_ih h.2]
    constructor <;> rfl
  | all T ih =>
    simp only [Ty.fv] at h
    specialize ih (k := k + 1) h
    simp only [openTy_all, subst_all, Ty.all.injEq]
    rw [ih]


/-
  Substituting a free variable that is not free in the type does nothing.
-/
@[simp]
lemma substTy_fresh {T : Ty} {X : Name} {U : Ty} (h : X ∉ T.fv) :
    T[X ↦ U] = T := by
  induction T with
  | bvar idx => rfl
  | fvar name =>
    simp only [subst_fvar, beq_iff_eq, ite_eq_right_iff]
    intro rfl
    simp [Ty.fv] at h
  | arr T₁ T₂ T₁_ih T₂_ih =>
    simp only [subst_arr, Ty.arr.injEq]
    simp [Ty.fv] at h
    simp_all only [not_false_eq_true, forall_const, and_self]
  | all T ih =>
    simp only [subst_all, Ty.all.injEq]
    simp only [Ty.fv] at h
    rw [ih h]

/-
  Opening a type with a free variable preserves the size of the type.
  Used to show termination.
-/
@[simp]
lemma openTy_size_fvar {T : Ty} {k : ℕ} {X : Name} :
    (T⟪k, $T X⟫).size = T.size := by
  induction T generalizing k with
  | bvar idx =>
    simp only [openTy_bvar, beq_iff_eq]
    dsimp [Ty.size]
    split <;> rfl
  | fvar name => dsimp [Open.open, openTy, Ty.size]
  | arr T₁ T₂ T₁_ih T₂_ih =>
    simp only [openTy_arr]
    dsimp [Ty.size]
    rw [T₁_ih, T₂_ih]
  | all T ih =>
    simp only [openTy_all]
    dsimp [Ty.size]
    rw [ih]


end SystemF

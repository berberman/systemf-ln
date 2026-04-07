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

instance : Open Ty Ty where
  «open» := openTy

@[simp]
lemma openTy_bvar {k : ℕ} {U : Ty} {x : ℕ} :
  (#T x)⟪k, U⟫ = if x == k then U else #T x := rfl

@[simp]
lemma openTy_fvar {k : ℕ} {U : Ty} {X : Name} :
  ($T X)⟪k, U⟫ = $T X := rfl

@[simp]
lemma openTy_arr {k : ℕ} {U T₁ T₂ : Ty} :
  (T₁ ⇒ T₂)⟪k, U⟫ = (T₁⟪k, U⟫ ⇒ T₂⟪k, U⟫) := rfl

@[simp]
lemma openTy_all {k : ℕ} {U T : Ty} :
  (∀' T)⟪k, U⟫ = ∀' (T⟪k + 1, U⟫) := rfl


/-
  Substitute free type variable `X` with `U` in `T`
-/
def substTy (X : Name) (U T : Ty) : Ty :=
  match T with
  | .bvar x => Ty.bvar x
  | .fvar Y => if X == Y then U else .fvar Y
  | .arr T₁ T₂ => .arr (substTy X U T₁) (substTy X U T₂)
  | .all T => Ty.all (substTy X U T)

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
  induction T generalizing k with simp [Ty.fv] at h
  | bvar idx =>
    simp
    split <;> aesop
  | _ => simp [*]


/-
  Substituting a free variable that is not free in the type does nothing.
-/
@[simp]
lemma substTy_fresh {T : Ty} {X : Name} {U : Ty} (h : X ∉ T.fv) :
    T[X ↦ U] = T := by
  induction T with (simp [Ty.fv] at h; simp [*])

/-
  Opening a type with a free variable preserves the size of the type.
  Used to show termination.
-/
@[simp]
lemma openTy_size_fvar {T : Ty} {k : ℕ} {X : Name} :
    (T⟪k, $T X⟫).size = T.size := by
  induction T generalizing k with simp [Ty.size, *] <;> split <;> rfl


end SystemF

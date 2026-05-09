import SystemF.Subst.Class

namespace SystemF

open Notation

/-- Open `T` with `U` at index `k`. -/
def Ty.open (T : Ty) (k : ℕ) (U : Ty) : Ty :=
  match T with
  | .bvar x => if x == k then U else .bvar x
  | .arr T₁ T₂ => .arr (T₁.open k U) (T₂.open k U)
  | .all T => .all (T.open (k + 1) U)
  | .fvar x => .fvar x

instance : Open Ty Ty where
  «open» k U T := T.open k U

@[simp, grind =]
lemma Ty.open_bvar {k : ℕ} {U : Ty} {x : ℕ} :
  (#T x)⟪k, U⟫ = if x == k then U else #T x := rfl

@[simp, grind =]
lemma Ty.open_fvar {k : ℕ} {U : Ty} {X : Name} :
  ($T X)⟪k, U⟫ = $T X := rfl

@[simp, grind =]
lemma Ty.open_arr {k : ℕ} {U T₁ T₂ : Ty} :
  (T₁ ⇒ T₂)⟪k, U⟫ = (T₁⟪k, U⟫ ⇒ T₂⟪k, U⟫) := rfl

@[simp, grind =]
lemma Ty.open_all {k : ℕ} {U T : Ty} :
  (∀' T)⟪k, U⟫ = ∀' (T⟪k + 1, U⟫) := rfl

/-- Substitute free type variable `X` with `U` in `T` -/
def Ty.subst (T : Ty) (X : Name) (U : Ty) : Ty :=
  match T with
  | .bvar x => .bvar x
  | .fvar Y => if X == Y then U else .fvar Y
  | .arr T₁ T₂ => .arr (T₁.subst X U) (T₂.subst X U)
  | .all T => .all (T.subst X U)

instance : Subst Ty Ty where
  subst X U T := T.subst X U

@[simp, grind =] lemma Ty.subst_bvar (X : Name) (U : Ty) (x : ℕ) :
  (Ty.bvar x)[X ↦ U] = Ty.bvar x := rfl

@[simp, grind =] lemma Ty.subst_fvar (X : Name) (U : Ty) (Y : Name) :
  (Ty.fvar Y)[X ↦ U] = if X == Y then U else Ty.fvar Y := rfl

@[simp, grind =] lemma Ty.subst_arr (X : Name) (U T₁ T₂ : Ty) :
  (Ty.arr T₁ T₂)[X ↦ U] = Ty.arr (T₁[X ↦ U]) (T₂[X ↦ U]) := rfl

@[simp, grind =] lemma Ty.subst_all (X : Name) (U T : Ty) :
  (Ty.all T)[X ↦ U] = Ty.all (T[X ↦ U]) := rfl

/-- Opening `T` with free variable `X` and then substituting `X` with `U` is the same as
  opening `T` with `U`, as long as `X` is not free in `T`.
-/
@[grind =]
theorem Ty.subst_open_var {k} {T U : Ty} {X : Name} (h : X ∉ T.fv) :
    (T⟪k, ($T X)⟫)[X ↦ U] = T⟪k, U⟫ := by
  induction T generalizing k <;> simp at * <;> grind

/-- Substituting a free variable that is not free in the type does nothing. -/
@[simp]
lemma Ty.subst_fresh {T : Ty} {X : Name} {U : Ty} (h : X ∉ T.fv) :
    T[X ↦ U] = T := by
  induction T <;> grind

end SystemF

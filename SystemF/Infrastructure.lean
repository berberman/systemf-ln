import SystemF.Syntax

namespace SystemF

/-
  Open `β` with `α` at index `k`, i.e. replacing bound variables at index `k` with `α` in `β`.
  `T⟪k, U⟫` opens `T` at index `k` with `U`.
  Here `T` is `β`, `k` is the index of the bound variable to be replaced, and `U` is `α`.
-/
class Open (α : Type) (β : Type) where
  «open» : ℕ → α → β → β

scoped notation T "⟪" k ", " U "⟫" => Open.open k U T
scoped notation T "⟪" U "⟫" => Open.open 0 U T

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
  Open `t` with `u` at index `k`.
-/
def openTm (k : ℕ) (u t : Tm) : Tm :=
  match t with
  | .bvar x => if x == k then u else .bvar x
  | .tLam t => .tLam (openTm k u t)
  | .lam ty t => .lam ty (openTm (k + 1) u t)
  | .app t₁ t₂ => .app (openTm k u t₁) (openTm k u t₂)
  | .tApp t T => .tApp (openTm k u t) T
  | .fvar x => .fvar x

@[simp]
instance : Open Tm Tm where
  «open» := openTm

@[simp]
lemma openTm_bvar {k : ℕ} {u : Tm} {x : ℕ} :
  (#v x)⟪k, u⟫ = if x == k then u else #v x := rfl

@[simp]
lemma openTm0_bvar {u : Tm} {x : ℕ} :
  (#v x)⟪u⟫ = if x == 0 then u else #v x := rfl

@[simp]
lemma openTm_fvar {k : ℕ} {u : Tm} {X : Name} :
  ($v X)⟪k, u⟫ = $v X := rfl

@[simp]
lemma openTm0_fvar {u : Tm} {X : Name} :
  ($v X)⟪u⟫ = $v X := rfl

@[simp]
lemma openTm_lam {k : ℕ} {u : Tm} {T : Ty} {t : Tm} :
  (ƛ T => t)⟪k, u⟫ = (ƛ T => t⟪k + 1, u⟫) := rfl

@[simp]
lemma openTm0_lam {u : Tm} {T : Ty} {t : Tm} :
  (ƛ T => t)⟪u⟫ = (ƛ T => t⟪1, u⟫) := rfl

@[simp]
lemma openTm_app {k : ℕ} {u : Tm} {t₁ t₂ : Tm} :
  (t₁ ◦ t₂)⟪k, u⟫ = (t₁⟪k, u⟫ ◦ t₂⟪k, u⟫) := rfl

@[simp]
lemma openTm0_app {u : Tm} {t₁ t₂ : Tm} :
  (t₁ ◦ t₂)⟪u⟫ = (t₁⟪u⟫ ◦ t₂⟪u⟫) := rfl

@[simp]
lemma openTm_tLam {k : ℕ} {u : Tm} {t : Tm} :
  (Λ' t)⟪k, u⟫ = Λ' (t⟪k, u⟫) := rfl

@[simp]
lemma openTm0_tLam {u : Tm} {t : Tm} :
  (Λ' t)⟪u⟫ = Λ' (t⟪u⟫) := rfl

@[simp]
lemma openTm_tApp {k : ℕ} {u : Tm} {t : Tm} {T : Ty} :
  (t ⦃T⦄)⟪k, u⟫ = (t⟪k, u⟫⦃T⦄) := rfl

@[simp]
lemma openTm0_tApp {u : Tm} {t : Tm} {T : Ty} :
  (t ⦃T⦄)⟪u⟫ = (t⟪u⟫⦃T⦄) := rfl

/-
  Open `t` with `U` at index `k`.
  Only handles type variables abstracted by `tLam`.
-/
def openTmTy (k : ℕ) (U : Ty) (t : Tm) : Tm :=
  match t with
  | .bvar x => .bvar x
  | .app t₁ t₂ => .app (openTmTy k U t₁) (openTmTy k U t₂)
  | .lam T' t => .lam (openTy k U T') (openTmTy (k + 1) U t)
  | .tLam t => .tLam (openTmTy (k + 1) U t)
  | .tApp t T' => .tApp (openTmTy k U t) (openTy k U T')
  | .fvar x => .fvar x

@[simp]
instance : Open Ty Tm where
  «open» := openTmTy

@[simp]
lemma openTmTy_bvar {k : ℕ} {U : Ty} {x : ℕ} :
  (#v x)⟪k, U⟫ = #v x := rfl

@[simp]
lemma openTmTy0_bvar {U : Ty} {x : ℕ} :
  (#v x)⟪U⟫ = #v x := rfl

@[simp]
lemma openTmTy_fvar {k : ℕ} {U : Ty} {X : Name} :
  ($v X)⟪k, U⟫ = $v X := rfl

@[simp]
lemma openTmTy0_fvar {U : Ty} {X : Name} :
  ($v X)⟪U⟫ = $v X := rfl

@[simp]
lemma openTmTy_lam {k : ℕ} {U : Ty} {T : Ty} {t : Tm} :
  (ƛ T => t)⟪k, U⟫ = (ƛ (T⟪k, U⟫) => t⟪k + 1, U⟫) := rfl

@[simp]
lemma openTmTy0_lam {U : Ty} {T : Ty} {t : Tm} :
  (ƛ T => t)⟪U⟫ = (ƛ (T⟪U⟫) => t⟪1, U⟫) := rfl

@[simp]
lemma openTmTy_app {k : ℕ} {U : Ty} {t₁ t₂ : Tm} :
  (t₁ ◦ t₂)⟪k, U⟫ = (t₁⟪k, U⟫ ◦ t₂⟪k, U⟫) := rfl

@[simp]
lemma openTmTy0_app {U : Ty} {t₁ t₂ : Tm} :
  (t₁ ◦ t₂)⟪U⟫ = (t₁⟪U⟫ ◦ t₂⟪U⟫) := rfl

@[simp]
lemma openTmTy_tLam {k : ℕ} {U : Ty} {t : Tm} :
  (Λ' t)⟪k, U⟫ = Λ' (t⟪k + 1, U⟫) := rfl

@[simp]
lemma openTmTy0_tLam {U : Ty} {t : Tm} :
  (Λ' t)⟪U⟫ = Λ' (t⟪1, U⟫) := rfl

@[simp]
lemma openTmTy_tApp {k : ℕ} {U : Ty} {t : Tm} {T : Ty} :
  (t ⦃T⦄)⟪k, U⟫ = (t⟪k, U⟫ ⦃T⟪k, U⟫⦄) := rfl

@[simp]
lemma openTmTy0_tApp {U : Ty} {t : Tm} {T : Ty} :
  (t ⦃T⦄)⟪U⟫ = (t⟪U⟫ ⦃T⟪U⟫⦄) := rfl


/-
  Substitute free variable with `α` in `β`.
  `T[X ↦ U]` substitutes free type variable `X` with `U` in `T`.
  Here `T` is `β`, `X` is `Name`, and `U` is `α`.
-/
class Subst (α : Type) (β : Type) where
  subst : Name → α → β → β

scoped notation T "[" X " ↦ " U "]" => Subst.subst X U T


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
  Substitute free type variable `X` with `U` in term `t`.
-/
def substTmTy (X : Name) (U : Ty) (t : Tm) : Tm :=
  match t with
  | .bvar idx => .bvar idx
  | .fvar name => .fvar name
  | .app t₁ t₂ => .app (substTmTy X U t₁) (substTmTy X U t₂)
  | .lam T t => .lam (substTy X U T) (substTmTy X U t)
  | .tLam t => .tLam (substTmTy X U t)
  | .tApp t T => .tApp (substTmTy X U t) (substTy X U T)

@[simp]
instance : Subst Ty Tm where
  subst := substTmTy

@[simp]
lemma substTmTy_bvar {X : Name} {U : Ty} {idx : ℕ} :
  (Tm.bvar idx)[X ↦ U] = Tm.bvar idx := rfl

@[simp]
lemma substTmTy_fvar {X : Name} {U : Ty} {name : Name} :
  (Tm.fvar name)[X ↦ U] = Tm.fvar name := rfl

@[simp]
lemma substTmTy_app {X : Name} {U : Ty} {t₁ t₂ : Tm} :
  (Tm.app t₁ t₂)[X ↦ U] = Tm.app (t₁[X ↦ U]) (t₂[X ↦ U]) := rfl

@[simp]
lemma substTmTy_lam {X : Name} {U : Ty} {T : Ty} {t : Tm} :
  (Tm.lam T t)[X ↦ U] = Tm.lam (T[X ↦ U]) (t[X ↦ U]) := rfl

@[simp]
lemma substTmTy_tLam {X : Name} {U : Ty} {t : Tm} :
  (Tm.tLam t)[X ↦ U] = Tm.tLam (t[X ↦ U]) := rfl

@[simp]
lemma substTmTy_tApp {X : Name} {U : Ty} {t : Tm} {T : Ty} :
  (Tm.tApp t T)[X ↦ U] = Tm.tApp (t[X ↦ U]) (T[X ↦ U]) := rfl

def substTm (X : Name) (u t : Tm) : Tm :=
  match t with
  | .bvar idx => .bvar idx
  | .fvar name => if name == X then u else .fvar name
  | .app t₁ t₂ => .app (substTm X u t₁) (substTm X u t₂)
  | .lam T t => .lam T (substTm X u t)
  | .tLam t => .tLam (substTm X u t)
  | .tApp t T => .tApp (substTm X u t) T

@[simp]
instance : Subst Tm Tm where
  subst := substTm

@[simp]
lemma substTm_bvar {X : Name} {u : Tm} {idx : ℕ} :
  (Tm.bvar idx)[X ↦ u] = Tm.bvar idx := rfl

@[simp]
lemma substTm_fvar {X : Name} {u : Tm} {name : Name} :
  (Tm.fvar name)[X ↦ u] = if name == X then u else Tm.fvar name := rfl

@[simp]
lemma substTm_app {X : Name} {u : Tm} {t₁ t₂ : Tm} :
  (Tm.app t₁ t₂)[X ↦ u] = Tm.app (t₁[X ↦ u]) (t₂[X ↦ u]) := rfl

@[simp]
lemma substTm_lam {X : Name} {u : Tm} {T : Ty} {t : Tm} :
  (Tm.lam T t)[X ↦ u] = Tm.lam T (t[X ↦ u]) := rfl

@[simp]
lemma substTm_tLam {X : Name} {u : Tm} {t : Tm} :
  (Tm.tLam t)[X ↦ u] = Tm.tLam (t[X ↦ u]) := rfl

@[simp]
lemma substTm_tApp {X : Name} {u : Tm} {t : Tm} {T : Ty} :
  (Tm.tApp t T)[X ↦ u] = Tm.tApp (t[X ↦ u]) T := rfl

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


@[simp]
lemma substTmTy_fresh {t : Tm} {X : Name} {U : Ty} (h : X ∉ t.fvTy) :
    t[X ↦ U] = t := by
  induction t with
  | bvar idx => simp
  | fvar name => simp
  | app t₁ t₂ t₁_ih t₂_ih =>
    simp
    simp [Tm.fvTy] at h
    simp_all only [not_false_eq_true, forall_const, and_self]
  | tApp t T ih =>
    simp only [substTmTy_tApp, Tm.tApp.injEq]
    simp only [Tm.fvTy, Finset.mem_union, not_or] at h
    constructor
    · apply ih h.1
    · apply substTy_fresh h.2
  | lam T t ih =>
    simp only [substTmTy_lam, Tm.lam.injEq]
    simp only [Tm.fvTy, Finset.mem_union, not_or] at h
    rw [ih h.2, substTy_fresh h.1]
    simp only [and_self]
  | tLam t ih =>
    simp only [substTmTy_tLam, Tm.tLam.injEq]
    simp only [Tm.fvTy] at h
    rw [ih h]


theorem openTm_substTmTy_comm {t u : Tm} {X : Name} {U : Ty} {k : ℕ} :
    (t[X ↦ U])⟪k, u[X ↦ U]⟫ = (t⟪k, u⟫)[X ↦ U]:= by
  induction t generalizing k with
  | bvar idx =>
    simp only [openTm_bvar, beq_iff_eq, substTmTy_bvar]
    dsimp [Subst.subst, substTmTy]
    split
    · aesop
    · rfl
  | fvar name => simp
  | app t₁ t₂ t₁_ih t₂_ih =>
    simp only [openTm_app, substTmTy_app, Tm.app.injEq]
    rw [t₁_ih, t₂_ih]
    simp_all only [and_self]
  | tApp t T ih =>
    simp only [openTm_tApp, substTmTy_tApp, Tm.tApp.injEq, and_true]
    rw [ih]
  | lam T t ih =>
    simp only [openTm_lam, substTmTy_lam, Tm.lam.injEq, true_and]
    rw [ih]
  | tLam t ih =>
    simp only [openTm_tLam, substTmTy_tLam, Tm.tLam.injEq]
    rw [ih]

theorem openTm_substTmTy_comm_fresh {t u : Tm} {X : Name} {U : Ty} {k : ℕ} (h : X ∉ u.fvTy) :
     (t[X ↦ U])⟪k, u⟫ = (t⟪k, u⟫)[X ↦ U] := by
  rw [←substTmTy_fresh h]
  rw [openTm_substTmTy_comm]
  rw [substTmTy_fresh h]

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

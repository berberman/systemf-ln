import SystemF.Subst.Ty
import SystemF.Subst.Tm

namespace SystemF

open Notation

/-- Open `t` with `U` at index `k`.
  Only handles type variables abstracted by `tLam`.
-/
def Tm.openTy (t : Tm) (k : ℕ) (U : Ty) : Tm :=
  match t with
  | .bvar x => .bvar x
  | .app t₁ t₂ => .app (t₁.openTy k U) (t₂.openTy k U)
  | .lam T' t => .lam (T'.open k U) (t.openTy k U)
  | .tLam t => .tLam (t.openTy (k + 1) U)
  | .tApp t T' => .tApp (t.openTy k U) (T'.open k U)
  | .fvar x => .fvar x

instance : Open Ty Tm where
  «open» k U t := t.openTy k U

@[simp, grind =]
lemma Tm.openTy_bvar {k : ℕ} {U : Ty} {x : ℕ} :
  (#v x)⟪k, U⟫ = #v x := rfl

@[simp, grind =]
lemma Tm.openTy_fvar {k : ℕ} {U : Ty} {X : Name} :
  ($v X)⟪k, U⟫ = $v X := rfl

@[simp, grind =]
lemma Tm.openTy_lam {k : ℕ} {U : Ty} {T : Ty} {t : Tm} :
  (ƛ T => t)⟪k, U⟫ = (ƛ (T⟪k, U⟫) => t⟪k, U⟫) := rfl

@[simp, grind =]
lemma Tm.openTy_app {k : ℕ} {U : Ty} {t₁ t₂ : Tm} :
  (t₁ ◦ t₂)⟪k, U⟫ = (t₁⟪k, U⟫ ◦ t₂⟪k, U⟫) := rfl

@[simp, grind =]
lemma Tm.openTy_tLam {k : ℕ} {U : Ty} {t : Tm} :
  (Λ' t)⟪k, U⟫ = Λ' (t⟪k + 1, U⟫) := rfl

@[simp, grind =]
lemma Tm.openTy_tApp {k : ℕ} {U : Ty} {t : Tm} {T : Ty} :
  (t ⦃T⦄)⟪k, U⟫ = (t⟪k, U⟫ ⦃T⟪k, U⟫⦄) := rfl

/-- Substitute free type variable `X` with `U` in term `t`. -/
def Tm.substTy (t : Tm) (X : Name) (U : Ty) : Tm :=
  match t with
  | .bvar idx => .bvar idx
  | .fvar name => .fvar name
  | .app t₁ t₂ => .app (t₁.substTy X U) (t₂.substTy X U)
  | .lam T t => .lam (T.subst X U) (t.substTy X U)
  | .tLam t => .tLam (t.substTy X U)
  | .tApp t T => .tApp (t.substTy X U) (T.subst X U)

instance : Subst Ty Tm where
  subst X U t := t.substTy X U

@[simp, grind =]
lemma Tm.substTy_bvar {X : Name} {U : Ty} {idx : ℕ} :
  (Tm.bvar idx)[X ↦ U] = Tm.bvar idx := rfl

@[simp, grind =]
lemma Tm.substTy_fvar {X : Name} {U : Ty} {name : Name} :
  (Tm.fvar name)[X ↦ U] = Tm.fvar name := rfl

@[simp, grind =]
lemma Tm.substTy_app {X : Name} {U : Ty} {t₁ t₂ : Tm} :
  (Tm.app t₁ t₂)[X ↦ U] = Tm.app (t₁[X ↦ U]) (t₂[X ↦ U]) := rfl

@[simp, grind =]
lemma Tm.substTy_lam {X : Name} {U : Ty} {T : Ty} {t : Tm} :
  (Tm.lam T t)[X ↦ U] = Tm.lam (T[X ↦ U]) (t[X ↦ U]) := rfl

@[simp, grind =]
lemma Tm.substTy_tLam {X : Name} {U : Ty} {t : Tm} :
  (Tm.tLam t)[X ↦ U] = Tm.tLam (t[X ↦ U]) := rfl

@[simp, grind =]
lemma Tm.substTy_tApp {X : Name} {U : Ty} {t : Tm} {T : Ty} :
  (Tm.tApp t T)[X ↦ U] = Tm.tApp (t[X ↦ U]) (T[X ↦ U]) := rfl

@[simp]
lemma Tm.substTy_fresh {t : Tm} {X : Name} {U : Ty} (h : X ∉ t.fvTy) :
    t[X ↦ U] = t := by
  induction t <;> grind [Ty.subst_fresh]

theorem Tm.open_substTy_comm {t u : Tm} {X : Name} {U : Ty} {k : ℕ} :
    (t[X ↦ U])⟪k, u[X ↦ U]⟫ = (t⟪k, u⟫)[X ↦ U] := by
  induction t generalizing k <;> grind

theorem Tm.open_substTy_comm_fresh {t u : Tm} {X : Name} {U : Ty} {k : ℕ}
    (h : X ∉ u.fvTy) :
    (t[X ↦ U])⟪k, u⟫ = (t⟪k, u⟫)[X ↦ U] := by
  rw [←Tm.substTy_fresh h]
  rw [Tm.open_substTy_comm]
  rw [Tm.substTy_fresh h]

@[grind =]
theorem Tm.substTy_openTy_var {t : Tm} {U : Ty} {X : Name} {k : ℕ}
    (h : X ∉ t.fvTy) :
    (t⟪k, $T X⟫)[X ↦ U] = t⟪k, U⟫ := by
  induction t generalizing k <;> grind

end SystemF

import SystemF.Subst.Ty
import SystemF.Subst.Tm

namespace SystemF

open Notation

/-- Open `t` with `U` at index `k`.
  Only handles type variables abstracted by `tLam`.
-/
def openTmTy (k : ℕ) (U : Ty) (t : Tm) : Tm :=
  match t with
  | .bvar x => .bvar x
  | .app t₁ t₂ => .app (openTmTy k U t₁) (openTmTy k U t₂)
  | .lam T' t => .lam (openTy k U T') (openTmTy k U t)
  | .tLam t => .tLam (openTmTy (k + 1) U t)
  | .tApp t T' => .tApp (openTmTy k U t) (openTy k U T')
  | .fvar x => .fvar x

instance : Open Ty Tm where
  «open» := openTmTy

@[simp]
lemma openTmTy_bvar {k : ℕ} {U : Ty} {x : ℕ} :
  (#v x)⟪k, U⟫ = #v x := rfl

@[simp]
lemma openTmTy_fvar {k : ℕ} {U : Ty} {X : Name} :
  ($v X)⟪k, U⟫ = $v X := rfl

@[simp]
lemma openTmTy_lam {k : ℕ} {U : Ty} {T : Ty} {t : Tm} :
  (ƛ T => t)⟪k, U⟫ = (ƛ (T⟪k, U⟫) => t⟪k, U⟫) := rfl

@[simp]
lemma openTmTy_app {k : ℕ} {U : Ty} {t₁ t₂ : Tm} :
  (t₁ ◦ t₂)⟪k, U⟫ = (t₁⟪k, U⟫ ◦ t₂⟪k, U⟫) := rfl

@[simp]
lemma openTmTy_tLam {k : ℕ} {U : Ty} {t : Tm} :
  (Λ' t)⟪k, U⟫ = Λ' (t⟪k + 1, U⟫) := rfl

@[simp]
lemma openTmTy_tApp {k : ℕ} {U : Ty} {t : Tm} {T : Ty} :
  (t ⦃T⦄)⟪k, U⟫ = (t⟪k, U⟫ ⦃T⟪k, U⟫⦄) := rfl

/-- Substitute free type variable `X` with `U` in term `t`. -/
def substTmTy (X : Name) (U : Ty) (t : Tm) : Tm :=
  match t with
  | .bvar idx => .bvar idx
  | .fvar name => .fvar name
  | .app t₁ t₂ => .app (substTmTy X U t₁) (substTmTy X U t₂)
  | .lam T t => .lam (substTy X U T) (substTmTy X U t)
  | .tLam t => .tLam (substTmTy X U t)
  | .tApp t T => .tApp (substTmTy X U t) (substTy X U T)

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

@[simp]
lemma substTmTy_fresh {t : Tm} {X : Name} {U : Ty} (h : X ∉ t.fvTy) :
    t[X ↦ U] = t := by
  induction t with aesop

@[simp]
theorem openTm_substTmTy_comm {t u : Tm} {X : Name} {U : Ty} {k : ℕ} :
    (t[X ↦ U])⟪k, u[X ↦ U]⟫ = (t⟪k, u⟫)[X ↦ U]:= by
  induction t generalizing k with aesop

@[simp]
theorem openTm_substTmTy_comm_fresh {t u : Tm} {X : Name} {U : Ty} {k : ℕ} (h : X ∉ u.fvTy) :
     (t[X ↦ U])⟪k, u⟫ = (t⟪k, u⟫)[X ↦ U] := by
  rw [←substTmTy_fresh h]
  rw [openTm_substTmTy_comm]
  rw [substTmTy_fresh h]


theorem substTmTy_openTmTy_var {t : Tm} {U : Ty} {X : Name} {k : ℕ} (h : X ∉ t.fvTy) :
    (t⟪k, $T X⟫)[X ↦ U] = t⟪k, U⟫ := by
  induction t generalizing k with aesop

end SystemF

import SystemF.Subst.Ty

namespace SystemF

open Notation

/-- Open `t` with `u` at index `k`. -/
def Tm.open (t : Tm) (k : ℕ) (u : Tm) : Tm :=
  match t with
  | .bvar x => if x == k then u else .bvar x
  | .tLam t => .tLam (t.open k u)
  | .lam ty t => .lam ty (t.open (k + 1) u)
  | .app t₁ t₂ => .app (t₁.open k u) (t₂.open k u)
  | .tApp t T => .tApp (t.open k u) T
  | .fvar x => .fvar x

instance : Open Tm Tm where
  «open» k u t := t.open k u

@[simp, grind =]
lemma Tm.open_bvar {k : ℕ} {u : Tm} {x : ℕ} :
  (#v x)⟪k, u⟫ = if x == k then u else #v x := rfl

@[simp, grind =]
lemma Tm.open_fvar {k : ℕ} {u : Tm} {X : Name} :
  ($v X)⟪k, u⟫ = $v X := rfl

@[simp, grind =]
lemma Tm.open_lam {k : ℕ} {u : Tm} {T : Ty} {t : Tm} :
  (ƛ T => t)⟪k, u⟫ = (ƛ T => t⟪k + 1, u⟫) := rfl

@[simp, grind =]
lemma Tm.open_app {k : ℕ} {u : Tm} {t₁ t₂ : Tm} :
  (t₁ ◦ t₂)⟪k, u⟫ = (t₁⟪k, u⟫ ◦ t₂⟪k, u⟫) := rfl

@[simp, grind =]
lemma Tm.open_tLam {k : ℕ} {u : Tm} {t : Tm} :
  (Λ' t)⟪k, u⟫ = Λ' (t⟪k, u⟫) := rfl

@[simp, grind =]
lemma Tm.open_tApp {k : ℕ} {u : Tm} {t : Tm} {T : Ty} :
  (t ⦃T⦄)⟪k, u⟫ = (t⟪k, u⟫⦃T⦄) := rfl

def Tm.subst (t : Tm) (X : Name) (u : Tm) : Tm :=
  match t with
  | .bvar idx => .bvar idx
  | .fvar name => if name == X then u else .fvar name
  | .app t₁ t₂ => .app (t₁.subst X u) (t₂.subst X u)
  | .lam T t => .lam T (t.subst X u)
  | .tLam t => .tLam (t.subst X u)
  | .tApp t T => .tApp (t.subst X u) T

instance : Subst Tm Tm where
  subst X u t := t.subst X u

@[simp, grind =]
lemma Tm.subst_bvar {X : Name} {u : Tm} {idx : ℕ} :
  (Tm.bvar idx)[X ↦ u] = Tm.bvar idx := rfl

@[simp, grind =]
lemma Tm.subst_fvar {X : Name} {u : Tm} {name : Name} :
  (Tm.fvar name)[X ↦ u] = if name == X then u else Tm.fvar name := rfl

@[simp, grind =]
lemma Tm.subst_app {X : Name} {u : Tm} {t₁ t₂ : Tm} :
  (Tm.app t₁ t₂)[X ↦ u] = Tm.app (t₁[X ↦ u]) (t₂[X ↦ u]) := rfl

@[simp, grind =]
lemma Tm.subst_lam {X : Name} {u : Tm} {T : Ty} {t : Tm} :
  (Tm.lam T t)[X ↦ u] = Tm.lam T (t[X ↦ u]) := rfl

@[simp, grind =]
lemma Tm.subst_tLam {X : Name} {u : Tm} {t : Tm} :
  (Tm.tLam t)[X ↦ u] = Tm.tLam (t[X ↦ u]) := rfl

@[simp, grind =]
lemma Tm.subst_tApp {X : Name} {u : Tm} {t : Tm} {T : Ty} :
  (Tm.tApp t T)[X ↦ u] = Tm.tApp (t[X ↦ u]) T := rfl

@[simp]
lemma Tm.subst_fresh {t : Tm} {X : Name} {u : Tm} (h : X ∉ t.fv) :
    t[X ↦ u] = t := by
  induction t <;> grind

@[grind =]
theorem Tm.subst_open_var {t u : Tm} {x : Name} {k : ℕ} (h : x ∉ t.fv) :
    (t⟪k, $v x⟫)[x ↦ u] = t⟪k, u⟫ := by
  induction t generalizing k <;> grind

end SystemF

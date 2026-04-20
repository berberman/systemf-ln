import SystemF.Subst.Ty

namespace SystemF

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

instance : Open Tm Tm where
  «open» := openTm

@[simp]
lemma openTm_bvar {k : ℕ} {u : Tm} {x : ℕ} :
  (#v x)⟪k, u⟫ = if x == k then u else #v x := rfl

@[simp]
lemma openTm_fvar {k : ℕ} {u : Tm} {X : Name} :
  ($v X)⟪k, u⟫ = $v X := rfl

@[simp]
lemma openTm_lam {k : ℕ} {u : Tm} {T : Ty} {t : Tm} :
  (ƛ T => t)⟪k, u⟫ = (ƛ T => t⟪k + 1, u⟫) := rfl

@[simp]
lemma openTm_app {k : ℕ} {u : Tm} {t₁ t₂ : Tm} :
  (t₁ ◦ t₂)⟪k, u⟫ = (t₁⟪k, u⟫ ◦ t₂⟪k, u⟫) := rfl

@[simp]
lemma openTm_tLam {k : ℕ} {u : Tm} {t : Tm} :
  (Λ' t)⟪k, u⟫ = Λ' (t⟪k, u⟫) := rfl

@[simp]
lemma openTm_tApp {k : ℕ} {u : Tm} {t : Tm} {T : Ty} :
  (t ⦃T⦄)⟪k, u⟫ = (t⟪k, u⟫⦃T⦄) := rfl

def substTm (X : Name) (u t : Tm) : Tm :=
  match t with
  | .bvar idx => .bvar idx
  | .fvar name => if name == X then u else .fvar name
  | .app t₁ t₂ => .app (substTm X u t₁) (substTm X u t₂)
  | .lam T t => .lam T (substTm X u t)
  | .tLam t => .tLam (substTm X u t)
  | .tApp t T => .tApp (substTm X u t) T

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

@[simp]
lemma substTm_fresh {t : Tm} {X : Name} {u : Tm} (h : X ∉ t.fv) :
    t[X ↦ u] = t := by
  induction t with aesop

theorem substTm_openTm_var {t u : Tm} {x : Name} {k : ℕ} (h : x ∉ t.fv) :
    (t⟪k, $v x⟫)[x ↦ u] = t⟪k, u⟫ := by
  induction t generalizing k with aesop

end SystemF

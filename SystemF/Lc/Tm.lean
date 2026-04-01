import SystemF.Lc.Ty
import SystemF.Subst.Tm
import SystemF.Subst.TyTm

namespace SystemF


/-
  Similar to `LcTy`, but for terms.
-/
inductive LcTm : Tm → Prop where
  | fvar x : LcTm ($v x)
  | app t₁ t₂ : LcTm t₁ → LcTm t₂ → LcTm (t₁ ◦ t₂)
  | lam (L : Finset Name) T t :
      LcTy T → (∀ x ∉ L, LcTm (t⟪$v x⟫)) → LcTm (ƛ T => t)
  | tApp t T : LcTm t → LcTy T → LcTm (t⦃T⦄)
  | tLam (L : Finset Name) t : (∀ X ∉ L, LcTm (t⟪$T X⟫)) → LcTm (Λ' t)

-- Example: `λ A => y 0` is a locally closed term
example : LcTm (ƛ ($T "A") => $v "y" ◦ #v 0) := by
  apply LcTm.lam {"y"}
  constructor
  intros
  repeat constructor

-- Example: `λ x : A -> 1` is not a locally closed term, because `1` is not properly bound
example : ¬ LcTm (ƛ ($T "A") => #v 1) := by
  intro h
  cases h with
  | lam L T t h₁ h₂ =>
    simp only [openTm_bvar, Nat.reduceBEq, Bool.false_eq_true, ↓reduceIte] at h₂
    have ⟨x, hx⟩ := exists_fresh_name L
    specialize h₂ x hx
    cases h₂

theorem openTm_neq_id {k j : ℕ} {t u v : Tm} (hNeq : k ≠ j) (h : t⟪j, v⟫⟪k, u⟫ = t⟪j, v⟫) :
    t⟪k, u⟫ = t := by
  induction t generalizing k j with
  | bvar idx =>
    simp at h
    by_cases idx = j
    · aesop
    · aesop
  | fvar name => simp
  | app t₁ t₂ t₁_ih t₂_ih => aesop
  | tApp t T ih => aesop
  | lam T t ih => aesop
  | tLam t ih => aesop

theorem openTm_eq_id {k j : ℕ} {t v : Tm} {U : Ty} (h : t⟪j, U⟫⟪k, v⟫ = t⟪j, U⟫) :
    t⟪k, v⟫ = t := by
  induction t generalizing k j with aesop

@[simp]
theorem openTm_lcTm_id {u : Tm} (h : LcTm u) (k : ℕ) (v : Tm) :
    u⟪k, v⟫ = u := by
  induction h generalizing k v with
  | fvar x => simp
  | app t₁ t₂ _ _ _ _ => aesop
  | lam L T t _ _ ih =>
    simp only [openTm_lam, Tm.lam.injEq, true_and]
    have ⟨x, hx⟩ := exists_fresh_name L
    have := ih x hx (k + 1) v
    have := @openTm_neq_id (k + 1) 0 t v ($vx) (by aesop) (by assumption)
    rw [this]
  | tApp t T _ _ _ => aesop
  | tLam L t _ ih =>
    simp only [openTm_tLam, Tm.tLam.injEq]
    have ⟨X, hX⟩ := exists_fresh_name L
    specialize ih X hX k v
    have := openTm_eq_id ih
    rw [this]

theorem openTm_substTm_comm {t u v : Tm} {X : Name} {k : ℕ} (hu : LcTm u) :
    (t[X ↦ u])⟪k, v[X ↦ u]⟫ = (t⟪k, v⟫)[X ↦ u]:= by
  induction t generalizing k with
  | bvar idx =>
    simp
    split <;> rfl
  | fvar name =>
    simp only [substTm_fvar, beq_iff_eq, openTm_fvar]
    split
    · rw [openTm_lcTm_id hu]
    · simp
  | app t₁ t₂ t₁_ih t₂_ih =>
    simp only [substTm_app, openTm_app, Tm.app.injEq]
    rw [t₁_ih, t₂_ih]
    simp_all only [and_self]
  | tApp t T ih =>
    simp only [substTm_tApp, openTm_tApp, Tm.tApp.injEq, and_true]
    rw [ih]
  | lam T t ih =>
    simp only [substTm_lam, openTm_lam, Tm.lam.injEq, true_and]
    rw [ih]
  | tLam t ih =>
    simp only [substTm_tLam, openTm_tLam, Tm.tLam.injEq]
    rw [ih]

theorem openTm_substTm_comm_of_neq {t u : Tm} {x y : Name} {k : ℕ}
    (hNeq : y ≠ x) (hu : LcTm u) :
    (t[x ↦ u])⟪k, $vy⟫ = (t⟪k, $vy⟫)[x ↦ u] := by
  rw [←openTm_substTm_comm hu]
  simp [hNeq]

end SystemF

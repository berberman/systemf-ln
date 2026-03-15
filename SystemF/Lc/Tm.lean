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

/-
  All bound *term* indices in `t` are strictly less than `k`.
  Note: it ignores bound type variables, so `LcAtTm 0` is not equivalent to `LcTm`.
-/
inductive LcAtTm : ℕ → Tm → Prop where
  | bvar i k : i < k → LcAtTm k (#v i)
  | fvar x k : LcAtTm k ($v x)
  | app t₁ t₂ k : LcAtTm k t₁ → LcAtTm k t₂ → LcAtTm k (t₁ ◦ t₂)
  | lam T t k : LcAtTm (k + 1) t → LcAtTm k (ƛ T => t)
  | tApp t T k : LcAtTm k t → LcAtTm k (t⦃T⦄)
  | tLam t k : LcAtTm k t → LcAtTm k (Λ' t)

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

theorem lcAtTm_openTm_id {t : Tm} {k : ℕ} (h : LcAtTm k t) (n : ℕ) (hn : k ≤ n) (u : Tm) :
    t⟪n, u⟫ = t := by
  induction h generalizing n with
  | bvar i k _ =>
    simp only [openTm_bvar, beq_iff_eq, ite_eq_right_iff]
    intro h
    omega
  | fvar x k => simp
  | app t₁ t₂ k _ _ ih₁ ih₂ =>
    simp only [openTm_app, Tm.app.injEq]
    rw [ih₁ _ hn, ih₂ _ hn]
    simp_all only [and_self]
  | lam T t k _ ih =>
    simp only [openTm_lam, Tm.lam.injEq, true_and]
    rw [ih (n + 1) (by omega)]
  | tApp t T k _ ih =>
    simp only [openTm_tApp, Tm.tApp.injEq, and_true]
    rw [ih _ hn]
  | tLam t k _ ih =>
    simp only [openTm_tLam, Tm.tLam.injEq]
    rw [ih _ hn]

theorem lcAtTm_of_openTm {t : Tm} {x : Name} {k : ℕ}
    (h : LcAtTm k (t⟪k, $vx⟫)) : LcAtTm (k + 1) t := by
  induction t generalizing k with
  | bvar idx =>
    simp only [openTm_bvar, beq_iff_eq] at h
    split at h
    · constructor
      omega
    · cases h
      constructor
      omega
  | fvar name => constructor
  | app t₁ t₂ t₁_ih t₂_ih =>
    cases h
    constructor
    · apply t₁_ih
      assumption
    · apply t₂_ih
      assumption
  | tApp t T ih =>
    cases h
    constructor
    · apply ih
      assumption
  | lam T t ih =>
    cases h
    constructor
    apply ih
    assumption
  | tLam t ih =>
    cases h
    constructor
    apply ih
    assumption

lemma lcAtTm_openTmTy_inv {t : Tm} {X : Name} {k n : ℕ}
    (h : LcAtTm k (t⟪n, $TX⟫)) : LcAtTm k t := by
  induction t generalizing k n with
  | bvar idx =>
    simp at h
    assumption
  | fvar name =>
    simp at h
    assumption
  | app t₁ t₂ t₁_ih t₂_ih =>
    cases h
    constructor
    · apply t₁_ih
      assumption
    · apply t₂_ih
      assumption
  | tApp t T ih =>
    cases h
    constructor
    · apply ih
      assumption
  | lam T t ih =>
    cases h
    constructor
    apply ih
    assumption
  | tLam t ih =>
    cases h
    constructor
    apply ih
    assumption

theorem lcTm_implies_lcAtTm0 {t : Tm} (h : LcTm t) : LcAtTm 0 t := by
  induction h with
  | fvar x => constructor
  | app t₁ t₂ _ _ ih₁ ih₂ =>
    constructor
    · apply ih₁
    · apply ih₂
  | lam L T t _ _ ih =>
    have ⟨x, hx⟩ := exists_fresh_name L
    specialize ih x hx
    constructor
    apply lcAtTm_of_openTm
    exact ih
  | tApp t T _ _ ih =>
    constructor
    assumption
  | tLam L t _ ih =>
    have ⟨X, hX⟩ := exists_fresh_name L
    specialize ih X hX
    constructor
    apply lcAtTm_openTmTy_inv
    exact ih

/-
  The converse does not hold: we don't track closedness of type variables in `LcAtTm`.
-/
theorem lcAtTm0_does_not_imply_lcTm : ∃ t, (LcAtTm 0 t ∧ ¬ LcTm t) := by
  use ƛ (#T 0) => $v "x"
  constructor
  · constructor
    constructor
  · intro h
    cases h with
    | lam L T t h₁ h₂ =>
      cases h₁

@[simp]
theorem openTm_lcTm_id {u : Tm} (h : LcTm u) (k : ℕ) (v : Tm) :
    u⟪k, v⟫ = u := by
  apply lcAtTm_openTm_id
  · apply lcTm_implies_lcAtTm0 h
  · simp only [zero_le]

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

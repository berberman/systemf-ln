import SystemF.Lc.Tm

namespace SystemF


/-
  All bound *type* indices inside the term `t` are strictly less than `k`.
  Note: it ignores bound term variables, so `LcAtTyTm 0` is not equivalent to `LcTm`.
-/
inductive LcAtTyTm : ℕ → Tm → Prop where
  | bvar i k : LcAtTyTm k (#v i)
  | fvar X k : LcAtTyTm k ($v X)
  | app t₁ t₂ k : LcAtTyTm k t₁ → LcAtTyTm k t₂ → LcAtTyTm k (t₁ ◦ t₂)
  | lam T t k : LcAtTy k T → LcAtTyTm k t → LcAtTyTm k (ƛ T => t)
  | tLam t k : LcAtTyTm (k + 1) t → LcAtTyTm k (Λ' t)
  | tApp t T k : LcAtTyTm k t → LcAtTy k T → LcAtTyTm k (t⦃T⦄)

theorem openTmTy_substTmTy_comm {t : Tm} {U : Ty} {X Y : Name} {k : ℕ}
    (hNeq : X ≠ Y) (hU : LcTy U) :
    (t[X ↦ U])⟪k, ($T Y)⟫ = (t⟪k, ($T Y)⟫)[X ↦ U] := by
  induction t generalizing k with
  | bvar idx => simp only [substTmTy_bvar, openTmTy_bvar]
  | fvar name => simp only [substTmTy_fvar, openTmTy_fvar]
  | app t₁ t₂ t₁_ih t₂_ih =>
    simp only [substTmTy_app, openTmTy_app, Tm.app.injEq]
    rw [t₁_ih, t₂_ih]
    simp_all only [ne_eq, and_self]
  | tApp t T ih =>
    simp only [substTmTy_tApp, openTmTy_tApp, Tm.tApp.injEq]
    rw [ih, openTy_substTy_comm hNeq hU]
    simp_all only [ne_eq, and_self]
  | lam T t ih =>
    simp only [substTmTy_lam, openTmTy_lam, Tm.lam.injEq]
    rw [ih, openTy_substTy_comm hNeq hU]
    simp_all only [ne_eq, and_self]
  | tLam t ih =>
    simp only [substTmTy_tLam, openTmTy_tLam, Tm.tLam.injEq]
    rw [ih]

theorem lcAtTyTm_openTmTy_id {t : Tm} {k : ℕ} (h : LcAtTyTm k t) (n : ℕ) (hn : k ≤ n) (V : Ty) :
    t⟪n, V⟫ = t := by
  induction h generalizing n with
  | bvar i k => simp
  | fvar X k => simp
  | app t₁ t₂ k _ _ ih₁ ih₂ =>
    simp only [openTmTy_app, Tm.app.injEq]
    rw [ih₁ _ hn, ih₂ _ hn]
    simp_all only [and_self]
  | lam T t k h _ ih =>
    simp only [openTmTy_lam, Tm.lam.injEq]
    rw [ih _ (by omega)]
    rw [lcAtTy_openTy_id h _ hn]
    simp_all only [and_self]
  | tLam t k _ ih =>
    simp only [openTmTy_tLam, Tm.tLam.injEq]
    rw [ih _ (by omega)]
  | tApp t T k _ h ih =>
    simp only [openTmTy_tApp, Tm.tApp.injEq]
    rw [ih _ hn]
    rw [lcAtTy_openTy_id h _ hn]
    simp_all only [and_self]

lemma lcAtTyTm_openTm_inv {t : Tm} {x : Name} {k n : ℕ}
    (h : LcAtTyTm k (t⟪n, $vx⟫)) : LcAtTyTm k t := by
  induction t generalizing k n with
  | bvar idx => constructor
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
    · assumption
  | lam T t ih =>
    cases h
    constructor
    · assumption
    · apply ih
      assumption
  | tLam t ih =>
    cases h
    constructor
    apply ih
    assumption

lemma lcAtTyTm_of_openTmTy {t : Tm} {X : Name} {k : ℕ}
    (h : LcAtTyTm k (t⟪k, $TX⟫)) : LcAtTyTm (k + 1) t := by
  induction t generalizing k with
  | bvar idx => constructor
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
    · apply lcAtTy_of_openTy
      assumption
  | lam T t ih =>
    cases h
    constructor
    · apply lcAtTy_of_openTy
      assumption
    · apply ih
      assumption
  | tLam t ih =>
    cases h
    constructor
    apply ih
    assumption

lemma lcTm_implies_lcAtTyTm0 {t : Tm} (h : LcTm t) : LcAtTyTm 0 t := by
  induction h with
  | fvar x => constructor
  | app t₁ t₂ _ _ _ _ => constructor <;> assumption
  | lam L T t _ _ ih =>
    constructor
    · apply lcTy_implies_lcAtTy0
      assumption
    · have ⟨x, hx⟩ := exists_fresh_name L
      specialize ih x hx
      apply lcAtTyTm_openTm_inv
      assumption
  | tApp t T _ _ ih =>
    constructor
    · apply ih
    · apply lcTy_implies_lcAtTy0
      assumption
  | tLam L t _ ih =>
    constructor
    have ⟨X, hX⟩ := exists_fresh_name L
    specialize ih X hX
    apply lcAtTyTm_of_openTmTy
    assumption

@[simp]
theorem openTmTy_lcTm_id {u : Tm} (hu : LcTm u) (k : ℕ) (V : Ty) :
    u⟪k, V⟫ = u := by
  apply lcAtTyTm_openTmTy_id
  · apply lcTm_implies_lcAtTyTm0 hu
  · simp only [zero_le]

theorem openTmTy_substTm_comm {t u : Tm} {x : Name} {V : Ty} {k : ℕ} (hu : LcTm u) :
    (t⟪k, V⟫)[x ↦ u] = (t[x ↦ u])⟪k, V⟫ := by
  induction t generalizing k with
  | bvar idx => simp
  | fvar name =>
    simp only [openTmTy_fvar, substTm_fvar, beq_iff_eq]
    split
    · rw [openTmTy_lcTm_id hu]
    · simp
  | app t₁ t₂ t₁_ih t₂_ih =>
    simp only [openTmTy_app, substTm_app, Tm.app.injEq]
    rw [t₁_ih, t₂_ih]
    simp_all only [and_self]
  | tApp t T ih =>
    simp only [openTmTy_tApp, substTm_tApp, Tm.tApp.injEq, and_true]
    rw [ih]
  | lam T t ih =>
    simp only [openTmTy_lam, substTm_lam, Tm.lam.injEq, true_and]
    rw [ih]
  | tLam t ih =>
    simp only [openTmTy_tLam, substTm_tLam, Tm.tLam.injEq]
    rw [ih]

end SystemF

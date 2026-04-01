import SystemF.Lc.Tm

namespace SystemF

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


theorem openTmTy_eq_id {k j : ℕ} {t u : Tm} {T : Ty} (h : t⟪j, u⟫⟪k, T⟫ = t⟪j, u⟫) :
    t⟪k, T⟫ = t := by
  induction t generalizing k j with aesop

theorem openTmTy_neq_id {k j : ℕ} {t : Tm} {T U : Ty} (hNeq : k ≠ j) (h : t⟪j, U⟫⟪k, T⟫ = t⟪j, U⟫) :
    t⟪k, T⟫ = t := by
  induction t generalizing k j with
  | bvar idx => simp
  | fvar name => simp
  | app t₁ t₂ t₁_ih t₂_ih => aesop
  | tApp t T ih =>
    simp only [openTmTy_tApp, Tm.tApp.injEq]
    simp only [openTmTy_tApp, Tm.tApp.injEq] at h
    constructor
    · apply ih (by aesop) h.1
    · apply openTy_neq_id (by aesop) h.2
  | lam T t ih =>
    simp only [openTmTy_lam, Tm.lam.injEq]
    simp only [openTmTy_lam, Tm.lam.injEq] at h
    constructor
    · apply openTy_neq_id (by aesop) h.1
    · apply ih (by aesop) h.2
  | tLam t ih => aesop

@[simp]
theorem openTmTy_lcTm_id {u : Tm} (hu : LcTm u) (k : ℕ) (V : Ty) :
    u⟪k, V⟫ = u := by
  induction hu generalizing k V with
  | fvar x => simp
  | app t₁ t₂ _ _ _ _ => aesop
  | lam L T t _ _ ih =>
    simp only [openTmTy_lam, Tm.lam.injEq]
    constructor
    · apply openTy_lcTy_id
      assumption
    · have ⟨x, hx⟩ := exists_fresh_name L
      specialize ih x hx k V
      have := openTmTy_eq_id ih
      rw [this]
  | tApp t T _ _ ih =>
    simp only [openTmTy_tApp, Tm.tApp.injEq]
    constructor
    · apply ih
    · apply openTy_lcTy_id
      assumption
  | tLam L _ _ ih =>
    simp only [openTmTy_tLam, Tm.tLam.injEq]
    have ⟨X, hX⟩ := exists_fresh_name L
    specialize ih X hX (k + 1) V
    have := openTmTy_neq_id (by aesop) ih
    rw [this]

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

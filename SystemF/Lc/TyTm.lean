import SystemF.Lc.Tm

namespace SystemF

@[aesop unsafe 70% apply]
theorem openTmTy_substTmTy_comm {t : Tm} {U : Ty} {X Y : Name} {k : ℕ}
    (hNeq : X ≠ Y) (hU : LcTy U) :
    (t[X ↦ U])⟪k, ($T Y)⟫ = (t⟪k, ($T Y)⟫)[X ↦ U] := by
  induction t generalizing k with aesop

@[aesop safe forward]
theorem openTmTy_eq_id {k j : ℕ} {t u : Tm} {T : Ty} (h : t⟪j, u⟫⟪k, T⟫ = t⟪j, u⟫) :
    t⟪k, T⟫ = t := by
  induction t generalizing k j with aesop

@[aesop safe forward]
theorem openTmTy_neq_id {k j : ℕ} {t : Tm} {T U : Ty} (hNeq : k ≠ j) (h : t⟪j, U⟫⟪k, T⟫ = t⟪j, U⟫) :
    t⟪k, T⟫ = t := by
  induction t generalizing k j with aesop

@[simp]
theorem openTmTy_lcTm_id {u : Tm} (hu : LcTm u) (k : ℕ) (V : Ty) :
    u⟪k, V⟫ = u := by
  induction hu generalizing k V with
  | fvar x => simp
  | app t₁ t₂ _ _ _ _ => aesop
  | lam L T t _ _ ih =>
    simp only [openTmTy_lam, Tm.lam.injEq]
    constructor
    · aesop
    · have ⟨x, hx⟩ := exists_fresh_name L
      specialize ih x hx k V
      have := openTmTy_eq_id ih
      rw [this]
  | tApp t T _ _ ih => aesop
  | tLam L _ _ ih =>
    simp only [openTmTy_tLam, Tm.tLam.injEq]
    have ⟨X, hX⟩ := exists_fresh_name L
    specialize ih X hX (k + 1) V
    have := openTmTy_neq_id (by aesop) ih
    rw [this]

@[aesop unsafe 70% apply]
theorem openTmTy_substTm_comm {t u : Tm} {x : Name} {V : Ty} {k : ℕ} (hu : LcTm u) :
    (t⟪k, V⟫)[x ↦ u] = (t[x ↦ u])⟪k, V⟫ := by
  induction t generalizing k with aesop

end SystemF

import SystemF.Lc.Tm

namespace SystemF

open Notation

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

@[aesop safe apply]
theorem substTm_lcTm {t u : Tm} {x : Name} (ht : LcTm t) (hu : LcTm u) : LcTm (t[x ↦ u]) := by
  induction ht generalizing x with
  | fvar y =>
    simp only [substTm_fvar, beq_iff_eq]
    split
    · assumption
    · constructor
  | app t₁ t₂ _ _ ih₁ ih₂ =>
    constructor
    · apply ih₁
    · apply ih₂
  | lam L T t _ _ ih =>
    simp only [substTm_lam]
    apply LcTm.lam (L ∪ {x})
    · assumption
    · intro y hy
      rw [openTm_substTm_comm_of_neq (by aesop) hu]
      apply ih
      aesop
  | tApp t T _ _ ih =>
    simp only [substTm_tApp]
    constructor
    · apply ih
    · assumption
  | tLam L t _ ih =>
    simp only [substTm_tLam]
    apply LcTm.tLam (L ∪ {x})
    intro Y hY
    rw [←openTmTy_substTm_comm hu]
    apply ih
    aesop

@[aesop safe apply]
theorem substTmTy_lcTm {t : Tm} {X : Name} {U : Ty} (ht : LcTm t)
    (hU : LcTy U) : LcTm (t[X ↦ U]) := by
  induction ht generalizing X with
  | fvar x => simp; constructor
  | app t₁ t₂ _ _ ih₁ ih₂ =>
    constructor
    · apply ih₁
    · apply ih₂
  | lam L T t _ _ ih =>
    apply LcTm.lam (L ∪ {X})
    · apply substTy_lcTy
      · assumption
      · assumption
    · intro y hy
      -- (t⟪k, u⟫)[X ↦ U]
      -- (substTmTy X U t⟪$vy⟫)
      change LcTm ((t[X ↦ U])⟪$vy⟫)
      rw [openTm_substTmTy_comm_fresh (by aesop)]
      apply ih
      aesop
  | tApp t T _ _ ih =>
    constructor
    · apply ih
    · apply substTy_lcTy
      · assumption
      · assumption
  | tLam L t _ ih =>
    apply LcTm.tLam (L ∪ {X})
    intro Y hY
    -- (substTmTy X U t⟪$TY⟫)
    -- (t⟪$TY⟫)[X ↦ U]
    change LcTm ((t[X ↦ U])⟪$TY⟫)
    rw [openTmTy_substTmTy_comm (by aesop) (by aesop)]
    apply ih
    aesop

@[aesop safe apply]
theorem openTm_lcTm {t u : Tm} {T : Ty} (ht : LcTm (ƛ T => t)) (hu : LcTm u) :
    LcTm (t⟪u⟫) := by
  cases ht with
  | lam L T t _ h =>
    have ⟨x, hx⟩ := exists_fresh_name (L ∪ t.fv)
    rw [←substTm_openTm_var (x:= x) (by aesop)]
    apply substTm_lcTm
    · apply h
      aesop
    · assumption

@[aesop safe apply]
theorem openTmTy_lcTm {t : Tm} {U : Ty} (ht : LcTm (Λ' t)) (hU : LcTy U) :
    LcTm (t⟪U⟫) := by
  cases ht with
  | tLam L t h =>
    have ⟨X, hX⟩ := exists_fresh_name (L ∪ t.fvTy)
    rw [←substTmTy_openTmTy_var (X := X) (by aesop)]
    apply substTmTy_lcTm _ hU
    aesop

theorem psubst_openTmTy_comm' {t : Tm} {U : Ty} {k} {X : Name} {γ : TmSubst} {δ : TySubst}
    (hX : X ∉ t.fvTy)
    (hγ : ∀ x, LcTm (γ x))
    (hδ : ∀ Y, LcTy (δ Y)) :
    (t.psubst γ δ)⟪k, U⟫ = (t⟪k, $TX⟫).psubst γ (Function.update δ X U) := by
  induction t generalizing X k with
  | bvar idx => rfl
  | fvar x =>
    simp only [Tm.psubst, openTmTy_fvar]
    rw [openTmTy_lcTm_id]
    apply hγ
  | app t₁ t₂ t₁_ih t₂_ih =>
    simp [Tm.psubst]
    aesop
  | tApp t T ih =>
    simp only [Tm.psubst, openTmTy_tApp, Tm.tApp.injEq]
    constructor
    · apply ih
      aesop
    · rw [psubst_openTy_comm']
      · aesop
      · assumption
  | lam T t ih =>
    simp only [Tm.psubst, openTmTy_lam, Tm.lam.injEq]
    constructor
    · rw [psubst_openTy_comm']
      · aesop
      · assumption
    · apply ih
      aesop
  | tLam t ih =>
    simp only [Tm.psubst, openTmTy_tLam, Tm.tLam.injEq]
    apply ih
    aesop

theorem psubst_openTmTy_comm {t : Tm} {k} {X : Name} {γ : TmSubst} {δ : TySubst}
    (hX : X ∉ t.fvTy)
    (hγ : ∀ x, LcTm (γ x))
    (hδ : ∀ Y, LcTy (δ Y)) :
    (t.psubst γ δ)⟪k, $TX⟫ = (t⟪k, $TX⟫).psubst γ (Function.update δ X ($TX)) := by
  apply psubst_openTmTy_comm' hX hγ hδ

lemma psubst_lcTm {t : Tm} (ht : LcTm t)
    {γ : TmSubst} {δ : TySubst}
    (hγ : ∀ x, LcTm (γ x))
    (hδ : ∀ X, LcTy (δ X)) :
    LcTm (t.psubst γ δ) := by
  induction ht generalizing γ δ with
  | fvar x => exact hγ x
  | app t₁ t₂ _ _ _ _ => constructor <;> aesop
  | lam L T t _ _ ih =>
    apply LcTm.lam (L ∪ t.fv)
    · apply psubst_lcTy <;> assumption
    · intro x hx
      rw [psubst_openTm_comm (by aesop) hγ]
      apply ih
      · aesop
      · intro y
        by_cases hy : y = x
        · subst hy
          simp
          constructor
        · aesop
      · assumption
  | tApp t T _ _ _ =>
    simp only [Tm.psubst]
    constructor
    · aesop
    · apply psubst_lcTy <;> assumption
  | tLam L t _ ih =>
    simp only [Tm.psubst]
    apply LcTm.tLam (L ∪ t.fvTy)
    intro X hX
    rw [psubst_openTmTy_comm (by aesop) hγ hδ]
    apply ih
    · aesop
    · intro y
      by_cases hY : y = X <;> aesop
    · intro Y
      by_cases hy : Y = X <;> aesop

end SystemF

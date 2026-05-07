import SystemF.Lc.Tm

namespace SystemF

open Notation

theorem openTmTy_substTmTy_comm {t : Tm} {U : Ty} {X Y : Name} {k : ℕ}
    (hNeq : X ≠ Y) (hU : LcTy U) :
    (t[X ↦ U])⟪k, ($T Y)⟫ = (t⟪k, ($T Y)⟫)[X ↦ U] := by
  induction t generalizing k <;> grind [openTy_substTy_comm]

lemma openTmTy_substTmTy_comm' {t : Tm} {X : Name} {U V : Ty} {k : ℕ}
    (hU : LcTy U) :
    (t[X ↦ U])⟪k, V[X ↦ U]⟫ = (t⟪k, V⟫)[X ↦ U] := by
  induction t generalizing k <;> grind [substTy_dist_openTy]

theorem openTmTy_eq_id {k j : ℕ} {t u : Tm} {T : Ty} (h : t⟪j, u⟫⟪k, T⟫ = t⟪j, u⟫) :
    t⟪k, T⟫ = t := by
  induction t generalizing k j <;> simp at * <;> grind [openTy_neq_id]

theorem openTmTy_neq_id {k j : ℕ} {t : Tm} {T U : Ty} (hNeq : k ≠ j) (h : t⟪j, U⟫⟪k, T⟫ = t⟪j, U⟫) :
    t⟪k, T⟫ = t := by
  induction t generalizing k j <;> simp at * <;> grind [openTy_neq_id]

@[simp]
theorem openTmTy_lcTm_id {u : Tm} (hu : LcTm u) (k : ℕ) (V : Ty) :
    u⟪k, V⟫ = u := by
  induction hu generalizing k V with
  | fvar x => simp
  | app t₁ t₂ _ _ _ _ => grind
  | lam L T t hT _ ih =>
    simp only [openTmTy_lam, Tm.lam.injEq]
    constructor
    · apply openTy_lcTy_id hT
    · have ⟨x, hx⟩ := exists_fresh_name L
      grind [openTmTy_eq_id]
  | tApp t T _ _ ih => grind [openTy_lcTy_id]
  | tLam L _ _ ih =>
    simp only [openTmTy_tLam, Tm.tLam.injEq]
    have ⟨X, hX⟩ := exists_fresh_name L
    grind [openTmTy_neq_id]

theorem openTmTy_substTm_comm {t u : Tm} {x : Name} {V : Ty} {k : ℕ} (hu : LcTm u) :
    (t⟪k, V⟫)[x ↦ u] = (t[x ↦ u])⟪k, V⟫ := by
  induction t generalizing k <;> grind [openTmTy_lcTm_id]

theorem substTm_lcTm {t u : Tm} {x : Name} (ht : LcTm t) (hu : LcTm u) : LcTm (t[x ↦ u]) := by
  induction ht generalizing x with
  | fvar y => grind [LcTm.fvar]
  | app t₁ t₂ _ _ ih₁ ih₂ => grind [LcTm.app]
  | lam L T t _ _ ih =>
    simp only [substTm_lam]
    apply LcTm.lam (L ∪ {x})
    · assumption
    · intro y hy
      grind [openTm_substTm_comm_of_neq]
  | tApp t T _ _ ih => grind [LcTm.tApp]
  | tLam L t _ ih =>
    simp only [substTm_tLam]
    apply LcTm.tLam (L ∪ {x})
    intro Y hY
    rw [←openTmTy_substTm_comm hu]
    apply ih
    grind

theorem substTmTy_lcTm {t : Tm} {X : Name} {U : Ty} (ht : LcTm t)
    (hU : LcTy U) : LcTm (t[X ↦ U]) := by
  induction ht generalizing X with
  | fvar x => simp; constructor
  | app t₁ t₂ _ _ ih₁ ih₂ => grind [LcTm.app]
  | lam L T t _ _ ih =>
    apply LcTm.lam (L ∪ {X})
    · apply substTy_lcTy
      · assumption
      · assumption
    · intro y hy
      -- (t⟪k, u⟫)[X ↦ U]
      -- (substTmTy X U t⟪$vy⟫)
      change LcTm ((t[X ↦ U])⟪$vy⟫)
      grind [openTm_substTmTy_comm_fresh]
  | tApp t T _ _ ih =>
    grind [substTy_lcTy, LcTm.tApp]
  | tLam L t _ ih =>
    apply LcTm.tLam (L ∪ {X})
    intro Y hY
    -- (substTmTy X U t⟪$TY⟫)
    -- (t⟪$TY⟫)[X ↦ U]
    change LcTm ((t[X ↦ U])⟪$TY⟫)
    grind [openTmTy_substTmTy_comm]

theorem openTm_lcTm {t u : Tm} {T : Ty} (ht : LcTm (ƛ T => t)) (hu : LcTm u) :
    LcTm (t⟪u⟫) := by
  cases ht with
  | lam L T t _ h =>
    have ⟨x, hx⟩ := exists_fresh_name (L ∪ t.fv)
    rw [←substTm_openTm_var (x:= x) (by grind)]
    apply substTm_lcTm
    · apply h
      grind
    · assumption

theorem openTmTy_lcTm {t : Tm} {U : Ty} (ht : LcTm (Λ' t)) (hU : LcTy U) :
    LcTm (t⟪U⟫) := by
  cases ht with
  | tLam L t h =>
    have ⟨X, hX⟩ := exists_fresh_name (L ∪ t.fvTy)
    rw [←substTmTy_openTmTy_var (X := X) (by grind)]
    apply substTmTy_lcTm _ hU
    grind

theorem psubst_openTmTy_comm' {t : Tm} {U : Ty} {k} {X : Name} {γ : TmSubst} {δ : TySubst}
    (hX : X ∉ t.fvTy)
    (hγ : ∀ x, LcTm (γ x))
    (hδ : ∀ Y, LcTy (δ Y)) :
    (t.psubst γ δ)⟪k, U⟫ = (t⟪k, $TX⟫).psubst γ (Function.update δ X U) := by
  induction t generalizing X k with grind [Tm.psubst, openTmTy_lcTm_id, psubst_openTy_comm']

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
  | app t₁ t₂ _ _ _ _ => grind [Tm.psubst, LcTm.app]
  | lam L T t _ _ ih =>
    apply LcTm.lam (L ∪ t.fv)
    · apply psubst_lcTy <;> assumption
    · grind [psubst_openTm_comm, LcTm.fvar]
  | tApp t T _ _ _ => grind [Tm.psubst, psubst_lcTy, LcTm.tApp]
  | tLam L t _ ih =>
    simp only [Tm.psubst]
    apply LcTm.tLam (L ∪ t.fvTy)
    grind [psubst_openTmTy_comm, LcTy.fvar]

end SystemF

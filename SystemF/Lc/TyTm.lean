import SystemF.Lc.Tm

namespace SystemF

open Notation

attribute [ln_norm_simps] Tm.open_substTy_comm_fresh

@[ln_norm_simps]
theorem Tm.openTy_substTy_comm {t : Tm} {U : Ty} {X Y : Name} {k : ℕ}
    (hNeq : X ≠ Y) (hU : LcTy U) :
    (t[X ↦ U])⟪k, ($T Y)⟫ = (t⟪k, ($T Y)⟫)[X ↦ U] := by
  induction t generalizing k <;> grind [Ty.open_subst_comm]

lemma Tm.openTy_substTy_comm_of_lc {t : Tm} {X : Name} {U V : Ty} {k : ℕ}
    (hU : LcTy U) :
    (t[X ↦ U])⟪k, V[X ↦ U]⟫ = (t⟪k, V⟫)[X ↦ U] := by
  induction t generalizing k <;> grind [Ty.subst_dist_open]

theorem Tm.openTy_eq_id {k j : ℕ} {t u : Tm} {T : Ty} (h : t⟪j, u⟫⟪k, T⟫ = t⟪j, u⟫) :
    t⟪k, T⟫ = t := by
  induction t generalizing k j <;> simp at * <;> grind [Ty.open_neq_id]

theorem Tm.openTy_neq_id {k j : ℕ} {t : Tm} {T U : Ty}
    (hNeq : k ≠ j) (h : t⟪j, U⟫⟪k, T⟫ = t⟪j, U⟫) :
    t⟪k, T⟫ = t := by
  induction t generalizing k j <;> simp at * <;> grind [Ty.open_neq_id]

@[simp]
theorem Tm.openTy_lc_id {u : Tm} (hu : LcTm u) (k : ℕ) (V : Ty) :
    u⟪k, V⟫ = u := by
  induction hu generalizing k V with
  | fvar x => simp
  | app t₁ t₂ _ _ _ _ => grind
  | lam L T t hT _ ih =>
    simp only [openTy_lam, lam.injEq]
    constructor
    · aesop
    · pick_fresh _; grind [openTy_eq_id]
  | tApp t T _ _ ih => grind [Ty.open_lc_id]
  | tLam L _ _ ih =>
    pick_fresh _
    grind [openTy_neq_id]

@[ln_norm_simps]
theorem Tm.openTy_subst_comm {t u : Tm} {x : Name} {V : Ty} {k : ℕ} (hu : LcTm u) :
    (t⟪k, V⟫)[x ↦ u] = (t[x ↦ u])⟪k, V⟫ := by
  induction t generalizing k <;> grind [openTy_lc_id]

@[aesop safe apply (rule_sets := [LcRules])]
theorem Tm.subst_lc {t u : Tm} {x : Name} (ht : LcTm t) (hu : LcTm u) : LcTm (t[x ↦ u]) := by
  induction ht generalizing x with
  | fvar y => grind [LcTm.fvar]
  | app t₁ t₂ _ _ ih₁ ih₂ => grind [LcTm.app]
  | lam L T t _ _ ih =>
    simp only [subst_lam]
    apply_cofinite
    · assumption
    · grind [open_subst_comm_of_neq]
  | tApp t T _ _ ih => grind [LcTm.tApp]
  | tLam L t _ ih =>
    simp only [subst_tLam]
    apply_cofinite
    intro Y hY
    rw [←openTy_subst_comm hu]
    apply ih
    grind

@[aesop safe apply (rule_sets := [LcRules])]
theorem Tm.substTy_lc {t : Tm} {X : Name} {U : Ty} (ht : LcTm t)
    (hU : LcTy U) : LcTm (t[X ↦ U]) := by
  induction ht generalizing X with ln_norm

@[grind ., aesop unsafe 50% apply (rule_sets := [LcRules])]
theorem Tm.open_lc {t u : Tm} {T : Ty} (ht : LcTm (ƛ T => t)) (hu : LcTm u) :
    LcTm (t⟪u⟫) := by
  cases ht with
  | lam L T t _ h =>
    pick_fresh x
    rw [←subst_open_var (x:= x) (by grind)]
    ln_norm

@[grind ., aesop unsafe 50% apply (rule_sets := [LcRules])]
theorem Tm.openTy_lc {t : Tm} {U : Ty} (ht : LcTm (Λ' t)) (hU : LcTy U) :
    LcTm (t⟪U⟫) := by
  cases ht with
  | tLam L t h =>
    pick_fresh X
    rw [←substTy_openTy_var (X := X) (by grind)]
    grind [substTy_lc]

theorem Tm.psubst_openTy_comm_update {t : Tm} {U : Ty} {k} {X : Name} {γ : TmSubst} {δ : TySubst}
    (hX : X ∉ t.fvTy)
    (hγ : ∀ x, LcTm (γ x))
    (hδ : ∀ Y, LcTy (δ Y)) :
    (t.psubst γ δ)⟪k, U⟫ = (t⟪k, $TX⟫).psubst γ (Function.update δ X U) := by
  induction t generalizing X k with grind [Tm.psubst, Tm.openTy_lc_id, Ty.psubst_open_comm_update]

theorem Tm.psubst_openTy_comm {t : Tm} {k} {X : Name} {γ : TmSubst} {δ : TySubst}
    (hX : X ∉ t.fvTy)
    (hγ : ∀ x, LcTm (γ x))
    (hδ : ∀ Y, LcTy (δ Y)) :
    (t.psubst γ δ)⟪k, $TX⟫ = (t⟪k, $TX⟫).psubst γ (Function.update δ X ($TX)) := by
  apply psubst_openTy_comm_update hX hγ hδ

@[aesop safe apply (rule_sets := [LcRules])]
lemma psubst_lcTm {t : Tm} (ht : LcTm t)
    {γ : TmSubst} {δ : TySubst}
    (hγ : ∀ x, LcTm (γ x))
    (hδ : ∀ X, LcTy (δ X)) :
    LcTm (t.psubst γ δ) := by
  induction ht generalizing γ δ with
  | fvar x => exact hγ x
  | app t₁ t₂ _ _ _ _ => grind [Tm.psubst, LcTm.app]
  | lam L T t _ _ ih =>
    apply_cofinite
    · apply psubst_lcTy <;> assumption
    · grind [Tm.psubst_open_comm, LcTm.fvar]
  | tApp t T _ _ _ => grind [Tm.psubst, psubst_lcTy, LcTm.tApp]
  | tLam L t _ ih =>
    apply_cofinite
    grind [Tm.psubst_openTy_comm, LcTy.fvar]

end SystemF

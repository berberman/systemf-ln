import SystemF.Lc.Ty
import SystemF.Subst.Tm
import SystemF.Subst.TyTm

namespace SystemF

open Notation

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

-- Example: `λ x : A -> #1` is not a locally closed term, because `#1` is out of scope.
example : ¬ LcTm (ƛ ($T "A") => #v 1) := by
  intro h
  cases h with
  | lam L T t h₁ h₂ =>
    simp only [openTm_bvar, Nat.reduceBEq, Bool.false_eq_true, ↓reduceIte] at h₂
    have ⟨x, hx⟩ := exists_fresh_name L
    specialize h₂ x hx
    cases h₂

@[aesop safe forward]
theorem openTm_neq_id {k j : ℕ} {t u v : Tm} (hNeq : k ≠ j) (h : t⟪j, v⟫⟪k, u⟫ = t⟪j, v⟫) :
    t⟪k, u⟫ = t := by
  induction t generalizing k j with aesop

@[aesop safe forward]
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

@[aesop unsafe 70% apply]
theorem openTm_substTm_comm {t u v : Tm} {X : Name} {k : ℕ} (hu : LcTm u) :
    (t[X ↦ u])⟪k, v[X ↦ u]⟫ = (t⟪k, v⟫)[X ↦ u]:= by
  induction t generalizing k with aesop

@[aesop safe forward]
theorem openTm_substTm_comm_of_neq {t u : Tm} {x y : Name} {k : ℕ}
    (hNeq : y ≠ x) (hu : LcTm u) :
    (t[x ↦ u])⟪k, $vy⟫ = (t⟪k, $vy⟫)[x ↦ u] := by
  rw [←openTm_substTm_comm hu]
  simp [hNeq]

theorem psubst_openTm_comm' {k} {t v : Tm} {x : Name} {γ : Name → Tm} {δ : Name → Ty}
    (hx : x ∉ t.fv)
    (hγ : ∀ y, LcTm (γ y)) :
    (t.psubst γ δ)⟪k, v⟫ = (t⟪k, $v x⟫).psubst (Function.update γ x v) δ := by
  induction t generalizing x k with
  | bvar idx =>
    simp [Tm.psubst]
    by_cases idx_eq : idx = k <;> simp [Tm.psubst, idx_eq]
  | fvar y =>
    have : y ≠ x := by aesop
    simp only [Tm.psubst, openTm_fvar, ne_eq, this, not_false_eq_true, Function.update_of_ne]
    rw [openTm_lcTm_id]
    apply hγ
  | app t₁ t₂ t₁_ih t₂_ih =>
    simp [Tm.psubst]
    aesop
  | tApp t T ih =>
    simp [Tm.psubst]
    aesop
  | lam T t ih =>
    simp [Tm.psubst]
    aesop
  | tLam t ih =>
    simp [Tm.psubst]
    aesop

theorem psubst_openTm_comm {k} {t : Tm} {x : Name} {γ : Name → Tm} {δ : Name → Ty}
    (hx : x ∉ t.fv)
    (hγ : ∀ y, LcTm (γ y)) :
    (t.psubst γ δ)⟪k, $v x⟫ = (t⟪k, $v x⟫).psubst (Function.update γ x ($v x)) δ := by
  apply psubst_openTm_comm' hx hγ

end SystemF

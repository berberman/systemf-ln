import SystemF.Lc.Ty
import SystemF.Subst.Tm
import SystemF.Subst.TyTm

namespace SystemF

open Notation

-- Example: `λ A => y 0` is a locally closed term
example : LcTm (ƛ ($T "A") => $v "y" ◦ #v 0) := by
  apply_cofinite
  constructor
  intros
  repeat constructor

-- Example: `λ x : A -> #1` is not a locally closed term, because `#1` is out of scope.
example : ¬ LcTm (ƛ ($T "A") => #v 1) := by
  intro h
  cases h with
  | lam L T t h₁ h₂ =>
    simp only [openTm_bvar, Nat.reduceBEq, Bool.false_eq_true, ↓reduceIte] at h₂
    pick_fresh x
    specialize h₂ x hx
    cases h₂

@[aesop safe forward]
theorem openTm_neq_id {k j : ℕ} {t u v : Tm} (hNeq : k ≠ j) (h : t⟪j, v⟫⟪k, u⟫ = t⟪j, v⟫) :
    t⟪k, u⟫ = t := by
  induction t generalizing k j <;> simp at * <;> grind

@[aesop safe forward]
theorem openTm_eq_id {k j : ℕ} {t v : Tm} {U : Ty} (h : t⟪j, U⟫⟪k, v⟫ = t⟪j, U⟫) :
    t⟪k, v⟫ = t := by
  induction t generalizing k j <;> simp at * <;> grind

@[simp]
theorem openTm_lcTm_id {u : Tm} (h : LcTm u) (k : ℕ) (v : Tm) :
    u⟪k, v⟫ = u := by
  induction h generalizing k v with
  | fvar x => simp
  | app t₁ t₂ _ _ _ _ => grind
  | lam L T t _ _ ih =>
    simp only [openTm_lam, Tm.lam.injEq, true_and]
    pick_fresh x
    have := ih x (by grind) (k + 1) v
    have := @openTm_neq_id (k + 1) 0 t v ($vx) (by grind) (by assumption)
    rw [this]
  | tApp t T _ _ _ => grind
  | tLam L t _ ih =>
    simp only [openTm_tLam, Tm.tLam.injEq]
    pick_fresh X
    specialize ih X (by grind) k v
    have := openTm_eq_id ih
    rw [this]

theorem openTm_substTm_comm {t u v : Tm} {X : Name} {k : ℕ} (hu : LcTm u) :
    (t[X ↦ u])⟪k, v[X ↦ u]⟫ = (t⟪k, v⟫)[X ↦ u]:= by
  induction t generalizing k <;> simp at * <;> grind [openTm_lcTm_id]

@[aesop safe forward]
theorem openTm_substTm_comm_of_neq {t u : Tm} {x y : Name} {k : ℕ}
    (hNeq : y ≠ x) (hu : LcTm u) :
    (t[x ↦ u])⟪k, $vy⟫ = (t⟪k, $vy⟫)[x ↦ u] := by
  rw [←openTm_substTm_comm hu]
  simp [hNeq]

theorem psubst_openTm_comm' {k} {t v : Tm} {x : Name} {γ : TmSubst} {δ : TySubst}
    (hx : x ∉ t.fv)
    (hγ : ∀ y, LcTm (γ y)) :
    (t.psubst γ δ)⟪k, v⟫ = (t⟪k, $v x⟫).psubst (Function.update γ x v) δ := by
  induction t generalizing x k with grind [Tm.psubst, openTm_lcTm_id]

theorem psubst_openTm_comm {k} {t : Tm} {x : Name} {γ : TmSubst} {δ : TySubst}
    (hx : x ∉ t.fv)
    (hγ : ∀ y, LcTm (γ y)) :
    (t.psubst γ δ)⟪k, $v x⟫ = (t⟪k, $v x⟫).psubst (Function.update γ x ($v x)) δ := by
  apply psubst_openTm_comm' hx hγ

end SystemF

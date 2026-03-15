import SystemF.Syntax
import SystemF.Lc.Ty
import SystemF.Lc.Tm

import Mathlib.Logic.Relation

namespace SystemF

inductive Value : Tm → Prop where
  | lam T t : Value (ƛ T => t)
  | tLam t : Value (Λ' t)

inductive SmallStep : Tm → Tm → Prop where
  | app₁ t₁ t₁' t₂ : LcTm t₂ → SmallStep t₁ t₁' → SmallStep (t₁ ◦ t₂) (t₁' ◦ t₂)
  | app₂ v t₂ t₂' : Value v → SmallStep t₂ t₂' → SmallStep (v ◦ t₂) (v ◦ t₂')
  | tApp t t' T : LcTy T → SmallStep t t' → SmallStep (t⦃T⦄) (t'⦃T⦄)
  | appLam t T v : LcTm (ƛ T => t) → Value v → SmallStep ((ƛ T => t) ◦ v) (t⟪v⟫)
  | tAppTLam t T : LcTm (Λ' t) → LcTy T → SmallStep ((Λ' t)⦃T⦄) (t⟪T⟫)

infix:50 " ⟶ " => SmallStep
infix:50 " ⟶* " => Relation.ReflTransGen SmallStep

lemma value_no_step {t t' : Tm} (h : Value t) (hStep : t ⟶ t') : False := by
  cases h <;> cases hStep

lemma small_step_deterministic {t t₁ t₂ : Tm}
    (h₁ : t ⟶ t₁) (h₂ : t ⟶ t₂) : t₁ = t₂ := by
  induction h₁ generalizing t₂ with
  | app₁ t₁ t₁' t₂ _ hStep _ =>
    cases h₂ with
    | app₁ t₁ t₁' t₂ _ _ => aesop
    | app₂ v t₂ t₂' _ _ =>
      exfalso
      apply value_no_step <;> assumption
    | appLam t T v _ _ => cases hStep
  | app₂ v t₂ t₂' _ hStep _ =>
    cases h₂ with
    | app₁ t₁ t₁' t₂ _ _ =>
      exfalso
      apply value_no_step <;> assumption
    | app₂ v t₂ t₂' _ _ => aesop
    | appLam t T v _ _ =>
      exfalso
      apply value_no_step <;> assumption
  | tApp t t' T _ hStep _ =>
    cases h₂ with
    | tApp t t' T _ _ => aesop
    | tAppTLam t T _ _ => cases hStep
  | appLam t T v _ _ =>
    cases h₂ with
    | app₁ t₁ t₁' t₂ _ h => cases h
    | app₂ v t₂ t₂' _ h =>
      exfalso
      apply value_no_step _ h
      assumption
    | appLam t T v _ _ => rfl
  | tAppTLam t T _ _ =>
    cases h₂ with
    | tApp t t' T _ h => cases h
    | tAppTLam t T _ _ => rfl



end SystemF

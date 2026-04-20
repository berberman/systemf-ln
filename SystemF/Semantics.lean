import SystemF.Syntax
import SystemF.Lc.Ty
import SystemF.Lc.Tm
import SystemF.Typing

import Mathlib.Logic.Relation

namespace SystemF

@[aesop safe cases]
inductive Value : Tm → Prop where
  | lam T t : Value (ƛ T => t)
  | tLam t : Value (Λ' t)

@[aesop unsafe cases 20%]
inductive SmallStep : Tm → Tm → Prop where
  | app₁ t₁ t₁' t₂ : LcTm t₂ → SmallStep t₁ t₁' → SmallStep (t₁ ◦ t₂) (t₁' ◦ t₂)
  | app₂ v t₂ t₂' : Value v → SmallStep t₂ t₂' → SmallStep (v ◦ t₂) (v ◦ t₂')
  | tApp t t' T : LcTy T → SmallStep t t' → SmallStep (t⦃T⦄) (t'⦃T⦄)
  | appLam t T v : LcTm (ƛ T => t) → Value v → SmallStep ((ƛ T => t) ◦ v) (t⟪v⟫)
  | tAppTLam t T : LcTm (Λ' t) → LcTy T → SmallStep ((Λ' t)⦃T⦄) (t⟪T⟫)

infix:50 " ⟶ " => SmallStep
infix:50 " ⟶* " => Relation.ReflTransGen SmallStep

@[aesop safe forward]
lemma value_no_step {t t' : Tm} (h : Value t) (hStep : t ⟶ t') : False := by
  cases h <;> cases hStep

@[aesop safe forward]
theorem small_step_deterministic {t t₁ t₂ : Tm}
    (h₁ : t ⟶ t₁) (h₂ : t ⟶ t₂) : t₁ = t₂ := by
  induction h₁ generalizing t₂ with (cases h₂ <;> aesop)

@[aesop safe forward]
lemma canonical_forms_arr {v : Tm} {T₁ T₂ : Ty}
    (hTyping : ∅ ⊢ v ∶ T₁ ⇒ T₂) (hVal : Value v) :
    ∃ t, v = (ƛ T₁ => t) := by aesop

@[aesop safe forward]
lemma canonical_forms_all {v : Tm} {T : Ty}
    (hTyping : ∅ ⊢ v ∶ ∀' T) (hVal : Value v) :
    ∃ t, v = (Λ' t) := by aesop

end SystemF

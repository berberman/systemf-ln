import SystemF.Lc.Tm
import SystemF.Lc.TyTm
import SystemF.Typing
import SystemF.CBV.Semantics

namespace SystemF.CBV

open Notation

theorem preservation {Γ : Context} {t t' : Tm} {T : Ty}
    (hTyping : Γ ⊢ t ∶ T) (hStep : t ⟶ t') :
    Γ ⊢ t' ∶ T := by
  induction hStep generalizing T with
  | app₁ t₁ t₁' t₂ _ _ _ =>
    cases hTyping
    constructor <;> aesop
  | app₂ v t₂ t₂' _ _ _ =>
    cases hTyping
    constructor <;> aesop
  | tApp t t' T _ _ _ =>
    cases hTyping
    constructor <;> aesop
  | appLam t T v _ _ =>
    cases hTyping with
    | app Γ t₁ t₂ T₁ T₂ hT₁ hT₂ =>
      cases hT₁ with
      | lam L Γ T₁ T₂ t _ hBody =>
        obtain ⟨x, hx⟩ := exists_fresh_name (L ∪ t.fv)
        have hx₁ : x ∉ L := by aesop
        have hx₂ : x ∉ t.fv := by aesop
        rw [←substTm_openTm_var hx₂]
        have := hBody x hx₁
        have := typing_subst_tm (Γ₁ := []) (Γ₂ := Γ) this (by aesop)
        simp only [List.nil_append] at this
        exact this
  | tAppTLam t T _ _ =>
    cases hTyping with
    | tApp Γ t T₁ T₂ hT₁ _ =>
      cases hT₁ with
      | tLam L Γ t T hBody =>
        obtain ⟨X, hX⟩ := exists_fresh_name (L ∪ T₁.fv ∪ t.fvTy ∪ Γ.fv)
        have hX₁ : X ∉ L := by aesop
        have hX₂ : X ∉ T₁.fv := by aesop
        have hX₃ : X ∉ t.fvTy := by aesop
        have hX₄ : X ∉ Γ.fv := by aesop
        rw [←substTy_openTy_var hX₂]
        rw [←substTmTy_openTmTy_var hX₃]
        have := hBody X hX₁
        have := typing_subst_ty (Γ₁ := []) this (by assumption)
        rw [substCtx_fresh hX₄] at this
        exact this

theorem progress {t : Tm} {T : Ty} (hTyping : ∅ ⊢ t ∶ T) :
    Value t ∨ ∃ t', t ⟶ t' := by
  generalize h : (∅ : Context) = Γ at hTyping
  induction hTyping with (subst h)
  | var Γ x T _ _ _ => contradiction
  | lam L Γ T₁ T₂ t _ _ _ => left; constructor
  | app Γ t₁ t₂ T₁ T₂ hTy₁ hTy₂ ih₁ ih₂ =>
    simp_all only [List.empty_eq, forall_const]
    cases ih₁ with
    | inl hV₁ =>
      cases ih₂ with
      | inl hV₂ =>
        obtain ⟨f, rfl⟩ := canonical_forms_arr hTy₁ hV₁
        right
        use f⟪t₂⟫
        constructor
        · exact typing_regularity_tm hTy₁
        · assumption
      | inr h =>
        obtain ⟨t₂', hStep⟩ := h
        right
        use t₁ ◦ t₂'
        constructor <;> assumption
    | inr h =>
      right
      obtain ⟨t₁', hStep⟩ := h
      use t₁' ◦ t₂
      constructor
      · exact typing_regularity_tm hTy₂
      · assumption
  | tLam L Γ t T _ _ => left; constructor
  | tApp Γ t T₁ T₂ hTy _ ih =>
    simp_all only [List.empty_eq, forall_const]
    cases ih with
    | inl hV =>
      obtain ⟨f, rfl⟩ := canonical_forms_all hTy hV
      right
      use f⟪T₂⟫
      constructor
      · exact typing_regularity_tm hTy
      · assumption
    | inr h =>
      obtain ⟨t', hStep⟩ := h
      right
      use t'⦃T₂⦄
      constructor <;> assumption

end SystemF.CBV

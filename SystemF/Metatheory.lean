import SystemF.Lc.Tm
import SystemF.Lc.TyTm
import SystemF.Typing
import SystemF.Semantics

namespace SystemF

/-- Inserting a new variable into a well-formed context preserves well-formedness,
  as long as the new variable is not free in the existing context.
-/
theorem typing_weakening {Γ₁ Γ₂ : Context} {t : Tm} {T : Ty} {x : Name} {b : Binding}
    (hTyping : (Γ₁ ++ Γ₂) ⊢ t ∶ T)
    (hWf : WfContext (Γ₁ ++ (x, b) :: Γ₂)) :
    (Γ₁ ++ (x, b) :: Γ₂) ⊢ t ∶ T := by
  generalize h : Γ₁ ++ Γ₂ = Γ at hTyping
  induction hTyping generalizing Γ₁ with
  | var Γ x T _ _ _ =>
    subst h
    constructor <;> aesop
  | lam L Γ T₁ T₂ t _ _ ih =>
    subst h
    let ctx := (Γ₁ ++ (x, b) :: Γ₂)
    apply HasType.lam (L ∪ ctx.dom)
    · assumption
    · intro y hy
      have hy₁ : y ∉ L := by aesop
      have hy₂ : y ∉ ctx.dom := by aesop
      have hWf_new : WfContext ((y, .tm T₁) :: Γ₁ ++ (x, b) :: Γ₂) := by
        constructor <;> assumption
      exact ih y hy₁ hWf_new rfl
  | app Γ t₁ t₂ T₁ T₂ _ _ ih₁ ih₂ =>
    constructor
    · apply ih₁ hWf h
    · apply ih₂ hWf h
  | tLam L Γ t T _ ih =>
    subst h
    let ctx := (Γ₁ ++ (x, b) :: Γ₂)
    apply HasType.tLam (L ∪ ctx.dom)
    intro Y hY
    have hY₁ : Y ∉ L := by aesop
    have hY₂ : Y ∉ ctx.dom := by aesop
    have hWf_new : WfContext ((Y, .ty) :: Γ₁ ++ (x, b) :: Γ₂) := by
      constructor <;> assumption
    exact ih Y hY₁ hWf_new rfl
  | tApp Γ t T₁ T₂ _ _ ih =>
    constructor
    · apply ih hWf h
    · assumption


/-- For `x : T` in `Γ`, substituting free variable `X` with `U` in `Γ`
  yields `(x, T[X ↦ U])` in `Γ[X ↦ U]`.
-/
theorem substCtx_lookup {Γ : Context} {x : Name} {T U : Ty} {X : Name}
    (h : (x, .tm T) ∈ Γ) :
    (x, .tm T[X ↦ U]) ∈ Γ[X ↦ U] := by
  induction Γ with
  | nil => simp only [substCtx_nil, List.not_mem_nil]; contradiction
  | cons head tail ih =>
    simp only [List.mem_cons] at h
    cases h with
    | inl h =>
      subst h
      simp only [substCtx_cons_tm, List.mem_cons, true_or]
    | inr h =>
      simp_all only [forall_const]
      rcases head with ⟨y, b⟩
      cases b with
      | ty => simp_all only [substCtx_cons_ty, List.mem_cons, Prod.mk.injEq, reduceCtorEq,
        and_false, or_true]
      | tm T => simp_all only [substCtx_cons_tm, List.mem_cons, Prod.mk.injEq, Binding.tm.injEq,
        or_true]

@[simp]
lemma substCtx_dom {Γ : Context} {X : Name} {U : Ty} :
    (Γ[X ↦ U]).dom = Γ.dom := by
  induction Γ with
  | nil => simp
  | cons head tail ih =>
    rcases head with ⟨y, b⟩
    cases b with
    | ty => simp_all only [substCtx_cons_ty, dom_cons, Finset.singleton_union]
    | tm T => simp_all only [substCtx_cons_tm, dom_cons, Finset.singleton_union]

lemma substCtx_wf {Γ : Context} {X : Name} {U : Ty}
    (hWf : WfContext Γ) (hU : LcTy U) : WfContext (Γ[X ↦ U]) := by
  induction hWf with
  | nil => simp; constructor
  | consTy Γ X _ _ ih =>
    simp only [substCtx_cons_ty]
    constructor
    · assumption
    · simp only [substCtx_dom]
      assumption
  | consTm Γ x T _ _ hLc ih =>
    simp only [substCtx_cons_tm]
    constructor
    · assumption
    · simp only [substCtx_dom]
      assumption
    · exact substTy_lcTy hLc hU

/-- Substitution lemma for types -/
theorem typing_subst_ty {Γ₁ Γ₂ : Context} {t : Tm} {T U : Ty} {X : Name}
    (hTyping : (Γ₁ ++ (X, .ty) :: Γ₂) ⊢ t ∶ T)
    (hLcTy : LcTy U) :
    (Γ₁[X ↦ U] ++ Γ₂[X ↦ U]) ⊢ (t[X ↦ U]) ∶ (T[X ↦ U]) := by
  generalize h : Γ₁ ++ (X, .ty) :: Γ₂ = Γ at hTyping
  induction hTyping generalizing Γ₁ with
  | var Γ x T hWf h₁ h₂ =>
    subst h
    constructor
    · have := wf_remove_mid hWf
      have := substCtx_wf this hLcTy (X := X)
      simp only at this
      rw [substCtx_append] at this
      exact this
    · simp only [List.mem_append, List.mem_cons, Prod.mk.injEq, reduceCtorEq, and_false,
      false_or] at h₁
      simp only [List.mem_append]
      cases h₁ with
      | inl h =>
        left
        apply substCtx_tm_mem
        assumption
      | inr h =>
        right
        apply substCtx_tm_mem
        assumption
    · exact substTy_lcTy h₂ hLcTy
  | lam L Γ T₁ T₂ t h₁ h₂ ih =>
    subst h
    apply HasType.lam (L ∪ {X} ∪ U.fv)
    · exact substTy_lcTy h₁ hLcTy
    · intro y hy
      have hy₁ : y ∉ L := by aesop
      -- ((y, .tm (substTy X U T₁)) :: (Γ₁[X ↦ U] ++ Γ₂[X ↦ U])) ⊢
      --  substTmTy X U t⟪$vy⟫ ∶ substTy X U T₂
      change ((y, .tm T₁[X ↦ U]) :: (Γ₁[X ↦ U] ++ Γ₂[X ↦ U])) ⊢ (t[X ↦ U])⟪$vy⟫ ∶ (T₂[X ↦ U])
      have := ih (Γ₁ := (y, Binding.tm T₁) :: Γ₁) y hy₁ rfl
      rw [openTm_substTmTy_comm_fresh]
      · exact this
      simp [Tm.fvTy]
  | app Γ t₁ t₂ T₁ T₂ _ _ ih₁ ih₂ =>
    simp only [substTmTy_app]
    constructor <;> aesop
  | tLam L Γ t T _ ih =>
    subst h
    apply HasType.tLam (L ∪ {X} ∪ U.fv)
    intro Y hY
    -- ((Y, .ty) :: (Γ₁[X ↦ U] ++ Γ₂[X ↦ U])) ⊢ substTmTy X U t⟪$TY⟫ ∶ substTy X U T⟪$TY⟫
    change ((Y, .ty) :: (Γ₁[X ↦ U] ++ Γ₂[X ↦ U])) ⊢ (t[X ↦ U])⟪$TY⟫ ∶ (T[X ↦ U])⟪$TY⟫
    have hY₁ : Y ∉ L := by aesop
    have hY₂ : X ≠ Y := by aesop
    rw [openTy_substTy_comm hY₂ hLcTy]
    rw [openTmTy_substTmTy_comm hY₂ hLcTy]
    have := ih (Γ₁ := (Y, .ty) :: Γ₁) Y hY₁ rfl
    exact this
  | tApp Γ t T₁ T₂ _ _ ih =>
    rw [substTy_dist_openTy hLcTy]
    constructor
    · aesop
    · apply substTy_lcTy <;> assumption

/-- Substitution lemma for terms -/
theorem typing_subst_tm {Γ₁ Γ₂ : Context} {t u : Tm} {T U : Ty} {x : Name}
    (hTyping : (Γ₁ ++ (x, .tm U) :: Γ₂) ⊢ t ∶ T)
    (hSubstTyping : (Γ₁ ++ Γ₂) ⊢ u ∶ U) :
    (Γ₁ ++ Γ₂) ⊢ (t[x ↦ u]) ∶ T := by
  generalize h : Γ₁ ++ (x, .tm U) :: Γ₂ = Γ at hTyping
  induction hTyping generalizing Γ₁ with
  | var Γ x' T _ _ _ =>
    simp only [substTm_fvar, beq_iff_eq]
    split
    · simp_all only
      rename_i hWf mem _ _
      subst h
      have : Binding.tm T = Binding.tm U := wf_lookup_mid hWf mem
      have : T = U := by injection this
      rw [this]
      assumption
    · subst h
      constructor
      · exact typing_regularity_wf hSubstTyping
      · aesop
      · assumption
  | lam L Γ T₁ T₂ t _ _ ih =>
    simp only [substTm_lam]
    apply HasType.lam (L ∪ {x} ∪ (Context.dom Γ))
    · assumption
    · intro y hy
      have hLCu : LcTm u := typing_regularity_tm hSubstTyping
      have hy₁ : y ∉ L := by aesop
      have hy₂ : y ≠ x := by aesop
      have hy₃ : y ∉ Context.dom (Γ₁ ++ Γ₂) := by aesop
      rw [openTm_substTm_comm_of_neq hy₂ hLCu]
      have : ((y, .tm T₁) :: Γ₁ ++ Γ₂) ⊢ u ∶ U := by
        have := typing_weakening (Γ₁ := []) (Γ₂ := Γ₁ ++ Γ₂) (x := y) (b := .tm T₁) hSubstTyping
        simp only [List.nil_append] at this
        apply this
        constructor
        · exact typing_regularity_wf hSubstTyping
        · exact hy₃
        · assumption
      -- Γ₁ ++ (x, .tm U) :: Γ₂ = (y, .tm T₁) :: (Γ₁ ++ (x, .tm U) :: Γ₂)
      exact @ih y hy₁ ((y, .tm T₁) :: Γ₁) this (by aesop)
  | app Γ t₁ t₂ T₁ T₂ _ _ ih₁ ih₂ =>
    subst h
    simp only [substTm_app]
    constructor
    · apply ih₁
      · assumption
      · rfl
    · apply ih₂
      · assumption
      · rfl
  | tLam L Γ t T _ ih =>
    simp only [substTm_tLam]
    apply HasType.tLam (L ∪ Context.dom Γ)
    intro Y hY
    have hLCu : LcTm u := typing_regularity_tm hSubstTyping
    have hY₁ : Y ∉ L := by aesop
    have hY₂ : Y ∉ Context.dom (Γ₁ ++ Γ₂) := by aesop
    rw [←openTmTy_substTm_comm hLCu]
    rw [←List.cons_append]
    apply ih
    · assumption
    · have : WfContext (Γ₁ ++ Γ₂) := typing_regularity_wf hSubstTyping
      exact typing_weakening (Γ₁ := []) hSubstTyping (by constructor <;> assumption)
    · aesop
  | tApp Γ t T₁ T₂ _ _ ih =>
    constructor
    apply ih <;> assumption
    assumption

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

end SystemF

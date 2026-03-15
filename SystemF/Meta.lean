import SystemF.Lc.Tm
import SystemF.Lc.TyTm
import SystemF.Typing

namespace SystemF

/-
  Inserting a new variable into a well-formed context preserves well-formedness,
  as long as the new variable is not free in the existing context.
-/
theorem typing_weakening {Γ₁ Γ₂ : Context} {t : Tm} {T U : Ty} {x : Name}
    (hTyping : (Γ₁ ++ Γ₂) ⊢ t ∶ T)
    (hWf : WfContext (Γ₁ ++ (x, U) :: Γ₂)) :
    (Γ₁ ++ (x, U) :: Γ₂) ⊢ t ∶ T := by
  generalize h : Γ₁ ++ Γ₂ = Γ at hTyping
  induction hTyping generalizing Γ₁ with
  | var Γ x T _ _ _ =>
    subst h
    constructor <;> aesop
  | lam L Γ T₁ T₂ t _ _ ih =>
    let ctx := (Γ₁ ++ (x, U) :: Γ₂)
    apply HasType.lam (L ∪ ctx.dom)
    · assumption
    · intro y hy
      have hy₁ : y ∉ L := by aesop
      have hy₂ : y ∉ ctx.dom := by aesop
      have hWf_new : WfContext ((y, T₁) :: ctx) := by
        constructor <;> assumption
      simp only [ctx] at hWf_new
      subst h
      have heq : (y, T₁) :: Γ₁ ++ Γ₂ = (y, T₁) :: (Γ₁ ++ Γ₂) := by simp
      have heq' : (y, T₁) :: (Γ₁ ++ (x, U) :: Γ₂) = ((y, T₁) :: Γ₁) ++ (x, U) :: Γ₂ := by simp
      have : WfContext (((y, T₁) :: Γ₁) ++ (x, U) :: Γ₂) := by
        rw [← heq']
        exact hWf_new
      exact ih y hy₁ this heq
  | app Γ t₁ t₂ T₁ T₂ _ _ ih₁ ih₂ =>
    constructor
    · apply ih₁ hWf h
    · apply ih₂ hWf h
  | tLam L Γ t T _ ih =>
    let ctx := (Γ₁ ++ (x, U) :: Γ₂)
    apply HasType.tLam (L ∪ ctx.fv)
    intro Y hY
    have hY₁ : Y ∉ L := by aesop
    exact ih Y hY₁ hWf h
  | tApp Γ t T₁ T₂ _ _ ih =>
    constructor
    · apply ih hWf h
    · assumption


/-
  For `x : T` in `Γ`, substituting free variable `X` with `U` in `Γ`
  yields `(x, T[X ↦ U])` in `Γ[X ↦ U]`.
-/
theorem substCtx_lookup {Γ : Context} {x : Name} {T U : Ty} {X : Name}
    (h : (x, T) ∈ Γ) :
    (x, T[X ↦ U]) ∈ Γ[X ↦ U] := by
  induction Γ with
  | nil => simp only [substCtx_nil, List.not_mem_nil]; contradiction
  | cons head tail ih =>
    simp only [List.mem_cons] at h
    cases h with
    | inl h =>
      subst h
      simp only [substCtx_cons, List.mem_cons, true_or]
    | inr h =>
      simp_all only [forall_const]
      cases head
      simp_all only [substCtx_cons, List.mem_cons, Prod.mk.injEq, or_true]

@[simp]
lemma substCtx_dom {Γ : Context} {X : Name} {U : Ty} :
    (Γ[X ↦ U]).dom = Γ.dom := by
  induction Γ with
  | nil => simp
  | cons head tail ih =>
    cases head
    simp only [substCtx_cons, dom_cons, Finset.singleton_union]
    rw [ih]

lemma substCtx_wf {Γ : Context} {X : Name} {U : Ty}
    (hWf : WfContext Γ) (hU : LcTy U) : WfContext (Γ[X ↦ U]) := by
  induction hWf with
  | nil => simp; constructor
  | cons Γ x T _ _ hLc ih =>
    simp only [substCtx_cons]
    constructor
    · assumption
    · simp only [substCtx_dom]
      assumption
    · exact substTy_lcTy hLc hU

/-
  Substitution lemma for types
-/
theorem typing_subst_ty {Γ : Context} {t : Tm} {T U : Ty} {X : Name}
    (hTyping : Γ ⊢ t ∶ T)
    (hLcTy : LcTy U) :
    (Γ[X ↦ U]) ⊢ (t[X ↦ U]) ∶ (T[X ↦ U]) := by
  induction hTyping with
  | var Γ x T hWf h₁ h₂ =>
    constructor
    · exact substCtx_wf hWf hLcTy
    · exact substCtx_lookup h₁
    · exact substTy_lcTy h₂ hLcTy
  | lam L Γ T₁ T₂ t h₁ h₂ ih =>
    apply HasType.lam (L ∪ {X} ∪ U.fv)
    · exact substTy_lcTy h₁ hLcTy
    · intro y hy
      have hy₁ : y ∉ L := by aesop
      specialize ih y hy₁
      -- ((y, substTy X U T₁) :: Γ[X ↦ U]) ⊢ substTmTy X U t⟪$vy⟫ ∶ substTy X U T₂
      change ((y, T₁[X ↦ U]) :: Γ[X ↦ U]) ⊢ (t[X ↦ U])⟪$vy⟫ ∶ (T₂[X ↦ U])
      rw [openTm_substTmTy_comm_fresh]
      · exact ih
      simp [Tm.fvTy]
  | app Γ t₁ t₂ T₁ T₂ _ _ ih₁ ih₂ =>
    simp only [substTmTy_app]
    constructor
    · apply ih₁
    · apply ih₂
  | tLam L Γ t T _ ih =>
    apply HasType.tLam (L ∪ {X} ∪ U.fv)
    intro Y hY
    -- Γ[X ↦ U] ⊢ substTmTy X U t⟪$TY⟫ ∶ substTy X U T⟪$TY⟫
    change (Γ[X ↦ U]) ⊢ (t[X ↦ U])⟪$TY⟫ ∶ (T[X ↦ U])⟪$TY⟫
    have hY₁ : Y ∉ L := by aesop
    have hY₂ : X ≠ Y := by aesop
    rw [openTy_substTy_comm hY₂ hLcTy]
    rw [openTmTy_substTmTy_comm hY₂ hLcTy]
    specialize ih Y hY₁
    exact ih
  | tApp Γ t T₁ T₂ _ _ ih =>
    simp only [substTmTy_tApp]
    rw [substTy_dist_openTy hLcTy]
    constructor
    · simp only [subst_all] at ih
      exact ih
    · apply substTy_lcTy <;> assumption

theorem typing_subst_tm {Γ₁ Γ₂ : Context} {t u : Tm} {T U : Ty} {x : Name}
    (hTyping : (Γ₁ ++ (x, U) :: Γ₂) ⊢ t ∶ T)
    (hSubstTyping : (Γ₁ ++ Γ₂) ⊢ u ∶ U) :
    (Γ₁ ++ Γ₂) ⊢ (t[x ↦ u]) ∶ T := by
  generalize h : Γ₁ ++ (x, U) :: Γ₂ = Γ at hTyping
  induction hTyping generalizing Γ₁ with
  | var Γ x' T _ _ _ =>
    simp only [substTm_fvar, beq_iff_eq]
    split
    · simp_all only
      rename_i hWf mem _ _
      subst h
      have : T = U := wf_lookup_mid hWf mem
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
      have : ((y, T₁) :: Γ₁ ++ Γ₂) ⊢ u ∶ U := by
        have := typing_weakening (Γ₁ := []) (Γ₂ := Γ₁ ++ Γ₂) (x := y) (U := T₁) hSubstTyping
        simp only [List.nil_append] at this
        apply this
        constructor
        · exact typing_regularity_wf hSubstTyping
        · exact hy₃
        · assumption
      -- Γ₁ ++ (x, U) :: Γ₂ = (y, T₁) :: (Γ₁ ++ (x, U) :: Γ₂)
      exact @ih y hy₁ ((y, T₁) :: Γ₁) this (by aesop)
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
    apply HasType.tLam (L ∪ {x} ∪ (Context.fv Γ))
    intro Y hY
    have hLCu : LcTm u := typing_regularity_tm hSubstTyping
    have hY₁ : Y ∉ L := by aesop
    rw [←openTmTy_substTm_comm hLCu]
    apply ih
    · assumption
    · assumption
    · aesop
  | tApp Γ t T₁ T₂ _ _ ih =>
    constructor
    apply ih <;> assumption
    assumption

end SystemF

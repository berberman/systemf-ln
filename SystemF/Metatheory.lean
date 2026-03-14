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
  | var Γ x T _ _ =>
    constructor
    · aesop
    · assumption
  | lam L Γ T₁ T₂ t _ _ ih =>
    let ctx := (Γ₁ ++ (x, U) :: Γ₂)
    apply HasType.lam (L ∪ ctx.fv)
    · assumption
    · intro y hy
      have hy₁ : y ∉ L := by aesop
      have hy₂ : y ∉ ctx.fv := by aesop
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
theorem subst_lookup {Γ : Context} {x : Name} {T U : Ty} {X : Name}
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


theorem typing_subst_ty {Γ : Context} {t : Tm} {T U : Ty} {X : Name}
    (hTyping : Γ ⊢ t ∶ T)
    (hLcTy : LcTy U) :
    (Γ[X ↦ U]) ⊢ (t[X ↦ U]) ∶ (T[X ↦ U]) := by
  induction hTyping with
  | var Γ x T h₁ h₂ =>
    constructor
    · apply subst_lookup h₁
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

end SystemF

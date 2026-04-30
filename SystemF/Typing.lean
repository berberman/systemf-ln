import SystemF.Context
import SystemF.Lc.Tm
import SystemF.Lc.TyTm

namespace SystemF

open Notation

/-- Typing relation -/
@[aesop unsafe cases 20%]
inductive HasType : Context → Tm → Ty → Prop where
  | var Γ x T :
    WfContext Γ →
    (x, .tm T) ∈ Γ →
    LcTy T →
    HasType Γ ($v x) T
  | lam (L : Finset Name) Γ T₁ T₂ t :
    LcTy T₁ →
    (∀ x ∉ L, HasType ((x, .tm T₁) :: Γ) (t⟪$v x⟫) T₂) →
    HasType Γ (ƛ T₁ => t) (T₁ ⇒ T₂)
  | app Γ t₁ t₂ T₁ T₂ :
    HasType Γ t₁ (T₁ ⇒ T₂) →
    HasType Γ t₂ T₁ →
    HasType Γ (t₁ ◦ t₂) T₂
  | tLam (L : Finset Name) Γ t T :
    (∀ X ∉ L, HasType ((X, .ty) :: Γ) (t⟪$T X⟫) (T⟪$T X⟫)) →
    HasType Γ (Λ' t) (∀' T)
  | tApp Γ t T₁ T₂ :
    HasType Γ t (∀' T₁) →
    LcTy T₂ →
    HasType Γ (t⦃T₂⦄) (T₁⟪T₂⟫)

scoped notation Γ " ⊢ " t " ∶ " T => HasType Γ t T

/-- Substitute free variable `X` with `U` in a context `Γ` (all types in `Γ` are substituted) -/
def substCtx (X : Name) (U : Ty) (Γ : Context) : Context :=
  Γ.map (fun ⟨y, b⟩ =>
    match b with
    | .ty => (y, .ty)
    | .tm T => (y, .tm (substTy X U T))
  )

@[simp]
instance : Subst Ty Context where
  subst := substCtx

@[simp]
lemma substCtx_nil {X : Name} {U : Ty} : ([][X ↦ U] : Context) = [] := rfl

@[simp]
lemma substCtx_cons_tm {Γ : Context} {X : Name} {U : Ty} {y : Name} {T : Ty} :
   ((y, .tm T) :: Γ)[X ↦ U] = (y, .tm T[X ↦ U]) :: Γ[X ↦ U] := rfl

@[simp]
lemma substCtx_cons_ty {Γ : Context} {X : Name} {U : Ty} {Y : Name} :
   ((Y, .ty) :: Γ)[X ↦ U] = (Y, .ty) :: Γ[X ↦ U] := rfl

/-- Substituting a free variable that is not free in the context does nothing. -/
@[simp]
lemma substCtx_fresh {Γ : Context} {X : Name} {U : Ty} (h : X ∉ Γ.fv) :
    Γ[X ↦ U] = Γ := by
  induction Γ with
  | nil => simp
  | cons head tail ih =>
    rcases head with ⟨y, b⟩
    cases b with
    | ty =>
      simp only [substCtx_cons_ty, List.cons.injEq, true_and]
      apply ih
      simp [Context.fv] at *
      aesop
    | tm T =>
      simp only [substCtx_cons_tm, List.cons.injEq, Prod.mk.injEq, Binding.tm.injEq, true_and]
      simp only [Context.fv, List.foldr_cons, Finset.mem_union, not_or] at *
      constructor
      · rw [substTy_fresh h.2]
      · aesop

lemma substCtx_append {Γ₁ Γ₂ : Context} {X : Name} {U : Ty} :
    (Γ₁ ++ Γ₂)[X ↦ U] = Γ₁[X ↦ U] ++ Γ₂[X ↦ U] := by
  induction Γ₁ with
  | nil => simp_all only [List.nil_append, substCtx_nil]
  | cons head tail ih =>
    simp only [List.cons_append]
    rcases head with ⟨y, b⟩
    cases b with
    | ty => aesop
    | tm T => aesop

lemma substCtx_tm_mem {Γ : Context} {x : Name} {T U : Ty} {X : Name}
    (h : (x, .tm T) ∈ Γ) :
    (x, .tm T[X ↦ U]) ∈ Γ[X ↦ U] := by
  exact List.mem_map_of_mem h
/-- Well-typed terms are locally closed terms. -/
lemma typing_regularity_tm {Γ t T} (h : Γ ⊢ t ∶ T) : LcTm t := by
  induction h with
  | var Γ x T _ _ _ =>
    constructor
  | lam L Γ T₁ T₂ t _ _ ih =>
    constructor
    · assumption
    · intro x h
      apply ih
      exact h
  | app Γ t₁ t₂ T₁ T₂ _ _ _ _ =>
    constructor <;> assumption
  | tLam L Γ t T _ ih =>
    constructor
    exact ih
  | tApp Γ t T₁ T₂ _ _ _ =>
    constructor <;> assumption

/-- Well-typed terms have locally closed types. -/
lemma typing_regularity_ty {Γ t T} (h : Γ ⊢ t ∶ T) : LcTy T := by
  induction h with
  | var Γ x T _ _ _ => assumption
  | lam L Γ T₁ T₂ t _ _ ih =>
    constructor
    · assumption
    · have ⟨x, hx⟩ := exists_fresh_name L
      apply ih
      exact hx
  | app Γ t₁ t₂ T₁ T₂ _ _ ih₁ ih₂ =>
    cases ih₁
    assumption
  | tLam L Γ t T _ ih =>
    apply LcTy.all L
    assumption
  | tApp Γ t T₁ T₂ _ _ ih =>
    apply openTy_lcTy ih
    assumption

/-- Well-typed terms have well-formed contexts. -/
lemma typing_regularity_wf {Γ t T} (h : Γ ⊢ t ∶ T) : WfContext Γ := by
  induction h with
  | var Γ x T _ _ _ => assumption
  | lam L Γ T₁ T₂ t _ _ ih =>
    have ⟨x, hx⟩ := exists_fresh_name L
    specialize ih x hx
    cases ih
    assumption
  | app Γ t₁ t₂ T₁ T₂ _ _ _ _ => assumption
  | tLam L Γ t T _ ih =>
    have ⟨X, hX⟩ := exists_fresh_name L
    specialize ih X hX
    exact wf_remove_mid (Γ₁ := []) (Γ₂ := Γ) ih
  | tApp Γ t T₁ T₂ _ _ _ => assumption


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

end SystemF

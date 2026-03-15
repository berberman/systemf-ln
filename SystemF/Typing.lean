import SystemF.LocallyClosed

namespace SystemF


abbrev Context := List (Name × Ty)

/-
  The free type variables in a context
-/
def Context.fv (Γ : Context) : Finset Name :=
  Γ.foldr (fun ⟨_, T⟩ acc => acc ∪ T.fv) ∅

/-
  Term variables in context
-/
def Context.dom (Γ : Context) : Finset Name :=
  Γ.foldr (fun ⟨x, _⟩ acc => acc ∪ {x}) ∅

@[simp]
lemma dom_nil : Context.dom [] = ∅ := rfl

@[simp]
lemma dom_cons {x : Name} {T : Ty} {Γ : Context} :
  Context.dom ((x, T) :: Γ) = {x} ∪ Γ.dom := by simp [Context.dom]

@[simp]
lemma dom_append {Γ₁ Γ₂ : Context} :
    (Γ₁ ++ Γ₂).dom = Γ₁.dom ∪ Γ₂.dom := by
  induction Γ₁ with
  | nil => simp only [List.nil_append, dom_nil, Finset.empty_union]
  | cons head tail ih =>
    cases head
    simp only [List.cons_append, dom_cons, Finset.singleton_union, Finset.insert_union]
    rw [ih]

lemma mem_dom_of_mem {Γ : Context} {x : Name} {T : Ty} (h : (x, T) ∈ Γ) : x ∈ Γ.dom := by
  induction Γ with
  | nil => contradiction
  | cons head tail ih =>
    cases head
    simp
    cases h
    · simp_all only [true_or]
    · aesop

/-
  Well-formed contexts: all types are locally closed and all variables are distinct.
-/
inductive WfContext : Context → Prop where
  | nil : WfContext []
  | cons Γ x T : WfContext Γ → x ∉ Γ.dom → LcTy T → WfContext ((x, T) :: Γ)

lemma wf_lookup_mid {Γ₁ Γ₂ : Context} {x : Name} {T U : Ty}
    (hWf : WfContext (Γ₁ ++ (x, U) :: Γ₂))
    (hMem : (x, T) ∈ Γ₁ ++ (x, U) :: Γ₂) :
    T = U := by
  induction Γ₁ with
  | nil =>
    simp_all only [List.nil_append, List.mem_cons, Prod.mk.injEq, true_and]
    cases hMem with
    | inl h => exact h
    | inr h =>
      cases hWf
      have := mem_dom_of_mem h
      contradiction
  | cons head tail ih =>
    rcases head with ⟨y, V⟩
    simp only [List.cons_append, List.mem_cons, Prod.mk.injEq, List.mem_append, true_and] at hMem
    cases hMem with
    | inl h =>
      cases hWf with
      | cons Γ x T _ _ _ => aesop
    | inr h =>
      cases hWf with
      | cons Γ x T _ _ _ => aesop

lemma wf_remove_mid {Γ₁ Γ₂ : Context} {x : Name} {U : Ty}
    (hWf : WfContext (Γ₁ ++ (x, U) :: Γ₂)) :
    WfContext (Γ₁ ++ Γ₂) := by
  induction Γ₁ with
  | nil => cases hWf with
    | cons Γ x T _ _ _ =>
      simp only [List.nil_append]
      assumption
  | cons head tail ih =>
    rcases head with ⟨y, V⟩
    simp only [List.cons_append]
    cases hWf with
    | cons Γ x T _ _ _ =>
      constructor
      · apply ih
        assumption
      · aesop
      · assumption


/-
  Typing relation
-/
inductive HasType : Context → Tm → Ty → Prop where
  | var Γ x T :
    WfContext Γ →
    (x, T) ∈ Γ →
    LcTy T →
    HasType Γ ($v x) T
  | lam (L : Finset Name) Γ T₁ T₂ t :
    LcTy T₁ →
    (∀ x ∉ L, HasType ((x, T₁) :: Γ) (t⟪$v x⟫) T₂) →
    HasType Γ (ƛ T₁ => t) (T₁ ⇒ T₂)
  | app Γ t₁ t₂ T₁ T₂ :
    HasType Γ t₁ (T₁ ⇒ T₂) →
    HasType Γ t₂ T₁ →
    HasType Γ (t₁ ◦ t₂) T₂
  | tLam (L : Finset Name) Γ t T :
    (∀ X ∉ L, HasType Γ (t⟪$T X⟫) (T⟪$T X⟫)) →
    HasType Γ (Λ' t) (∀' T)
  | tApp Γ t T₁ T₂ :
    HasType Γ t (∀' T₁) →
    LcTy T₂ →
    HasType Γ (t⦃T₂⦄) (T₁⟪T₂⟫)

scoped notation Γ " ⊢ " t " ∶ " T => HasType Γ t T

/-
  Substituting free variable `X` with `U` in a context `Γ` (all types in `Γ` are substituted).
-/
def substCtx (X : Name) (U : Ty) (Γ : Context) : Context :=
  Γ.map (fun ⟨y, T⟩ => (y, substTy X U T))

@[simp]
instance : Subst Ty Context where
  subst := substCtx

@[simp]
lemma substCtx_nil {X : Name} {U : Ty} : ([][X ↦ U] : Context) = [] := rfl

@[simp]
lemma substCtx_cons {Γ : Context} {X : Name} {U : Ty} {y : Name} {T : Ty} :
   ((y, T) :: Γ)[X ↦ U] = (y, T[X ↦ U]) :: Γ[X ↦ U] := rfl

/-
  Substituting a free variable that is not free in the context does nothing.
-/
@[simp]
lemma substCtx_fresh {Γ : Context} {X : Name} {U : Ty} (h : X ∉ Γ.fv) :
    Γ[X ↦ U] = Γ := by
  induction Γ with
  | nil => simp
  | cons head tail ih =>
    rcases head with ⟨y, T⟩
    simp only [substCtx_cons, List.cons.injEq, Prod.mk.injEq, true_and]
    simp only [Context.fv, List.foldr] at *
    simp_all only [Finset.mem_union, not_or, not_false_eq_true, substTy_fresh, and_self]


/-
  Well-typed terms are locally closed terms.
-/
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

/-
  Well-typed terms have locally closed types.
-/
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

/-
  Well-typed terms have well-formed contexts.
-/
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
    assumption
  | tApp Γ t T₁ T₂ _ _ _ => assumption

end SystemF

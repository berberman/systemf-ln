import SystemF.Context
import SystemF.Lc.Tm

namespace SystemF

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

end SystemF

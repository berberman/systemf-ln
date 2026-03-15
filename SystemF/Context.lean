import SystemF.Lc.Ty

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

end SystemF

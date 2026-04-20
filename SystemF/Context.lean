import SystemF.Lc.Ty

namespace SystemF

inductive Binding where
  /--
    Type variable binding
  -/
  | ty
  /--
    Term variable binding with its type
  -/
  | tm (T : Ty)
deriving Repr, DecidableEq

def Binding.fv : Binding → Finset Name
  | .ty => ∅
  | .tm T => T.fv

abbrev Context := List (Name × Binding)

/-- Free type variables in a context -/
def Context.fv (Γ : Context) : Finset Name :=
  Γ.foldr (fun ⟨_, b⟩ acc => acc ∪ b.fv) ∅

/-- All variables in context -/
def Context.dom (Γ : Context) : Finset Name :=
  Γ.foldr (fun ⟨x, _⟩ acc => acc ∪ {x}) ∅

@[simp]
lemma dom_nil : Context.dom [] = ∅ := rfl

@[simp]
lemma dom_cons {x : Name} {b : Binding} {Γ : Context} :
    Context.dom ((x, b) :: Γ) = {x} ∪ Γ.dom := by simp [Context.dom]

@[simp]
lemma dom_cons_tm {x : Name} {T : Ty} {Γ : Context} :
  Context.dom ((x, .tm T) :: Γ) = {x} ∪ Γ.dom := by simp [Context.dom]

@[simp]
lemma dom_cons_ty {X : Name} {Γ : Context} :
  Context.dom ((X, .ty) :: Γ) = {X} ∪ Γ.dom := by simp [Context.dom]

@[simp]
lemma dom_append {Γ₁ Γ₂ : Context} :
    (Γ₁ ++ Γ₂).dom = Γ₁.dom ∪ Γ₂.dom := by
  induction Γ₁ with
  | nil => simp only [List.nil_append, dom_nil, Finset.empty_union]
  | cons head tail ih =>
    rcases head with ⟨k, v⟩
    cases v with simp_all

lemma mem_dom_of_mem {Γ : Context} {x : Name} {b : Binding} (h : (x, b) ∈ Γ) : x ∈ Γ.dom := by
  induction Γ with
  | nil => contradiction
  | cons head tail ih =>
    rcases head with ⟨y, v⟩
    cases v with aesop

/-- In well-formed contexts all types are locally closed and all variables are distinct. -/
inductive WfContext : Context → Prop where
  | nil : WfContext []
  | consTm Γ x T : WfContext Γ → x ∉ Γ.dom → LcTy T → WfContext ((x, .tm T) :: Γ)
  | consTy Γ X : WfContext Γ → X ∉ Γ.dom → WfContext ((X, .ty) :: Γ)

lemma wf_lookup_mid {Γ₁ Γ₂ : Context} {x : Name} {b₁ b₂ : Binding}
    (hWf : WfContext (Γ₁ ++ (x, b₁) :: Γ₂))
    (hMem : (x, b₂) ∈ Γ₁ ++ (x, b₁) :: Γ₂) :
    b₂ = b₁ := by
  induction Γ₁ with
  | nil =>
    simp_all only [List.nil_append, List.mem_cons, Prod.mk.injEq, true_and]
    cases hMem with
    | inl h => exact h
    | inr h =>
      cases hWf <;> (have := mem_dom_of_mem h; contradiction)
  | cons head tail ih =>
    rcases head with ⟨y, V⟩
    simp_all only [List.mem_append, List.mem_cons, Prod.mk.injEq, true_and, List.cons_append]
    cases hMem with
    | inl h =>
      cases hWf with
      | consTm Γ x T _ _ _ => aesop
      | consTy Γ X _ _ => aesop
    | inr h =>
      cases hWf with
      | consTm Γ x T _ _ _ => aesop
      | consTy Γ X _ _ => aesop

lemma wf_remove_mid {Γ₁ Γ₂ : Context} {x : Name} {b : Binding}
    (hWf : WfContext (Γ₁ ++ (x, b) :: Γ₂)) :
    WfContext (Γ₁ ++ Γ₂) := by
  induction Γ₁ with
  | nil => cases hWf with
    | consTm Γ x T _ _ _ => aesop
    | consTy Γ X _ _ => aesop
  | cons head tail ih =>
    rcases head with ⟨y, V⟩
    simp only [List.cons_append]
    cases hWf with
    | consTm Γ x T _ _ _ =>
      constructor <;> aesop
    | consTy Γ X _ _ =>
      constructor <;> aesop

end SystemF

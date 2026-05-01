import SystemF.Typing

namespace SystemF

open Notation

namespace StronglyNormalization

inductive Neutral : Tm → Prop
  | fvar {x} : Neutral ($vx)
  | bvar {idx} : Neutral (#vidx)
  | app {t₁ t₂} : Neutral (t₁ ◦ t₂)
  | tApp {t T} : Neutral (t⦃T⦄)

inductive Step : Tm → Tm → Prop
  | app₁ {t₁ t₁' t₂} : Step t₁ t₁' → Step (t₁ ◦ t₂) (t₁' ◦ t₂)
  | app₂ {t₁ t₂ t₂'} : Step t₂ t₂' → Step (t₁ ◦ t₂) (t₁ ◦ t₂')
  | tApp₁ {t t' T} : Step t t' → Step (t⦃T⦄) (t'⦃T⦄)
  | tLamBody {t t'} : Step t t' → Step (Λ' t) (Λ' t')
  | lamBody {T t t'} : Step t t' → Step (ƛ T => t) (ƛ T => t')
  | appLam {T t₁ t₂} : LcTm (ƛ T => t₁) → LcTm t₂ → Step ((ƛ T => t₁) ◦ t₂) (t₁⟪t₂⟫)
  | tAppTLam {t T} : LcTm (Λ' t) → LcTy T → Step ((Λ' t)⦃T⦄) (t⟪T⟫)

scoped infix:50 " ⟶ " => Step
scoped infix:50 " ⟶* " => Relation.ReflTransGen Step

abbrev BackwardsStep := flip Step

scoped infix:50 " ⟵ " => BackwardsStep
scoped infix:50 " *⟵ " => Relation.ReflTransGen BackwardsStep

@[simp]
lemma step_of_backwards_step {t t' : Tm} : (t ⟵ t') = (t' ⟶ t) := rfl

theorem step_openTmTy {t t' : Tm} (hStep : t ⟶ t') (k : ℕ) (U : Ty) :
    t⟪k, U⟫ ⟶ t'⟪k, U⟫ := by
  induction hStep generalizing k with
  | app₁ _ _ => constructor; aesop
  | app₂ _ _ => constructor; aesop
  | tApp₁ _ _ => constructor; aesop
  | tLamBody _ _ => constructor; aesop
  | lamBody _ _ => constructor; aesop
  | appLam _ _ =>
    simp
    sorry
  | tAppTLam _ _ => sorry

theorem step_openTm {t t' : Tm} (hStep : t ⟶ t') (k : ℕ) (u : Tm) (hu : LcTm u) :
    t⟪k, u⟫ ⟶ t'⟪k, u⟫ := by sorry

theorem lcTm_step {t t' : Tm} (h : LcTm t) (hStep : t ⟶ t') : LcTm t' := by
  induction hStep with
  | app₁ _ _ => cases h; constructor <;> aesop
  | app₂ _ _ => cases h; constructor <;> aesop
  | tApp₁ _ _ => cases h; constructor <;> aesop
  | tLamBody _ ih =>
    cases h with
    | tLam L t h =>
      apply LcTm.tLam L
      intro X hX
      sorry
  | lamBody _ _ => sorry
  | appLam _ _ => cases h; aesop
  | tAppTLam _ _ => cases h; aesop

/--
`t` is strongly normalizing if there exists no infinite sequence
`t ⟶ t₁ ⟶ t₂ ⟶ t₃ ...`, or equivalently:
`... ⟵ t₃ ⟵ t₂ ⟵ t₁ ⟵ t`, i.e. no infinite descending sequence of backwards steps.
So here we use `Acc` with `≤` to be `⟵` to define strong normalization.
-/
abbrev SN (t : Tm) : Prop := Acc BackwardsStep t

structure RC (S : Set Tm) : Prop where
  /-- Every term in the set is locally closed -/
  lc : ∀ {t}, t ∈ S → LcTm t
  /-- Every term in the set is strongly normalizing -/
  cr₁ : ∀ {t}, t ∈ S → SN t
  /-- Closed under reduction -/
  cr₂ : ∀ {t t'}, t ∈ S → t ⟶ t' → t' ∈ S
  /-- Closed under backwards reduction for neutrals -/
  cr₃ : ∀ {t}, LcTm t → Neutral t → (∀ t', t ⟶ t' → t' ∈ S) → t ∈ S

lemma RC.cr₂_multi {S : Set Tm} (hRC : RC S) {t t'} (ht : t ∈ S) (hSteps : t ⟶* t') : t' ∈ S := by
  induction hSteps with
  | refl => assumption
  | tail _ _ ih =>
    apply hRC.cr₂
    · apply ih
    · assumption

lemma multi_step_openTm {t x x' : Tm} (hStep : x ⟶ x') : t⟪x⟫ ⟶* t⟪x'⟫ := by
  induction hStep with
  | app₁ _ _ => sorry
  | app₂ _ _ => sorry
  | tApp₁ _ _ => sorry
  | tLamBody _ _ => sorry
  | lamBody _ _ => sorry
  | appLam _ _ => sorry
  | tAppTLam _ _ => sorry

lemma fvar_in_RC {X : Name} {S : Set Tm} (h : RC S) : $vX ∈ S := by
  apply h.cr₃
  · constructor
  · constructor
  · intro t hStep
    cases hStep

lemma sn_of_sn_app {t u : Tm} (h : SN (t ◦ u)) : SN t := by
  generalize hEq : t ◦ u = tu at h
  induction h generalizing t u with subst hEq
  | intro x h ih =>
    constructor
    intro t' hStep
    have : (t ◦ u) ⟶ (t' ◦ u) := Step.app₁ hStep
    exact ih (t' ◦ u) this rfl

def arr_set (S₁ S₂ : Set Tm) : Set Tm := { t | ∀ u ∈ S₁, (t ◦ u) ∈ S₂ }

scoped notation S₁ " ⇒ " S₂ => arr_set S₁ S₂

theorem RC_arr {S₁ S₂ : Set Tm} (h₁ : RC S₁) (h₂ : RC S₂) : RC (S₁ ⇒ S₂) := by
  constructor
  · intro t h
    simp only [arr_set, Set.mem_setOf_eq] at h
    let x := $v"dummy"
    have : x ∈ S₁ := fvar_in_RC h₁
    have : (t ◦ x) ∈ S₂ := h _ this
    have := h₂.lc this
    cases this with
    | app t₁ t₂ _ _ => assumption
  · intro t h
    let x := $v"dummy"
    have : x ∈ S₁ := fvar_in_RC h₁
    have : (t ◦ x) ∈ S₂ := h _ this
    have := h₂.cr₁ this
    apply sn_of_sn_app
    assumption
  · intro t t' h hStep u hu
    have : (t ◦ u) ⟶ (t' ◦ u) := Step.app₁ hStep
    exact h₂.cr₂ (h _ hu) this
  · intro t hLc hNeu h u hu
    have := h₁.cr₁ hu
    induction this with
    | intro u _ ih =>
      apply h₂.cr₃
      · constructor
        · assumption
        · exact h₁.lc hu
      · constructor
      · intro v hStep
        cases hStep with
        | app₁ hStep₁ =>
          have := h _ hStep₁
          apply this
          assumption
        | app₂ hStep₂ =>
          apply ih
          · assumption
          · apply h₁.cr₂ hu hStep₂
        | appLam _ _ => cases hNeu

def sn_set : Set Tm := { t | LcTm t ∧ SN t }

@[simp]
theorem RC_sn : RC sn_set := by
  constructor
  · intro t h
    exact h.1
  · intro t h
    exact h.2
  · intro t t' h hStep
    constructor
    · have : LcTm t := h.1
      apply lcTm_step this hStep
    · exact h.2.inv hStep
  · intro t hLc hNeu h
    constructor
    · assumption
    · simp only [sn_set, Set.mem_setOf_eq] at h
      apply Acc.intro
      intro t' hStep
      have := h t' hStep |>.2
      apply this

def all_set (F : Set Tm → Set Tm) : Set Tm := ⋂ S ∈ { S | RC S }, F S

scoped notation "∀' " F => all_set F

theorem RC_all {F : Set Tm → Set Tm} (hF : ∀ S, RC S → RC (F S)) : RC (∀' F) := by
  constructor
  · intro t h
    simp only [all_set, Set.mem_setOf_eq, Set.mem_iInter] at h
    have hNorm := h sn_set RC_sn
    have hRC := hF sn_set RC_sn
    apply hRC.lc
    assumption
  · intro t h
    simp only [all_set, Set.mem_setOf_eq, Set.mem_iInter] at h
    have hNorm := h sn_set RC_sn
    have hRC := hF sn_set RC_sn
    apply hRC.cr₁
    assumption
  · intro t t' h hStep
    simp only [all_set, Set.mem_setOf_eq, Set.mem_iInter] at *
    intro S hS
    have := hF S hS
    apply this.cr₂ _ hStep
    apply h
    assumption
  · intro t hLc hNeu h
    simp only [all_set, Set.mem_setOf_eq, Set.mem_iInter] at *
    intro S hS
    have := hF S hS
    apply this.cr₃ hLc hNeu
    intro t' hStep
    apply h <;> assumption

structure SemEnv where
  bound : List (Set Tm)
  free  : Name → Set Tm

structure SemEnv.IsValid (ρ : SemEnv) : Prop where
  free_rc : ∀ X, RC (ρ.free X)
  bound_rc : ∀ S ∈ ρ.bound, RC S

def SemEnv.empty : SemEnv := { bound := [], free := fun _ => sn_set }

@[simp]
theorem semEnv_empty_valid : SemEnv.empty.IsValid := by
  constructor
  · intro X
    simp [SemEnv.empty]
  · intro S
    simp [SemEnv.empty]

theorem semEnv_valid_extend_bound {ρ : SemEnv} {S : Set Tm} (hValid : ρ.IsValid) (hS : RC S) :
    { ρ with bound := S :: ρ.bound }.IsValid := by
  constructor
  · intro X
    apply hValid.free_rc
  · intro S' hS'
    simp only [List.mem_cons] at hS'
    cases hS' with
    | inl h => aesop
    | inr h => apply hValid.bound_rc; assumption

def _root_.SystemF.Ty.interp (T : Ty) (ρ : SemEnv) : Set Tm :=
  match T with
  | .bvar idx => if h : idx < ρ.bound.length then ρ.bound[idx] else sn_set
  | .fvar X => ρ.free X
  | .arr T₁ T₂ => arr_set (T₁.interp ρ) (T₂.interp ρ)
  | .all T => all_set (fun S => T.interp { ρ with bound := S :: ρ.bound })

/-- If the environment only contains valid `RC`s, the interpreted type is a valid `RC`. -/
theorem interp_soundness (T : Ty) {ρ : SemEnv} (hValid : ρ.IsValid) : RC (T.interp ρ) := by
  induction T generalizing ρ with
  | bvar idx =>
    simp only [Ty.interp]
    by_cases h : idx < ρ.bound.length
    · simp only [h, ↓reduceDIte]
      apply hValid.bound_rc
      simp
    · simp [h]
  | fvar X => apply hValid.free_rc
  | arr T₁ T₂ ih₁ ih₂ => apply RC_arr <;> aesop
  | all T ih =>
    apply RC_all
    intro S hS
    apply ih
    apply semEnv_valid_extend_bound hValid hS

structure EnvRel (Γ : Context) (ρ : SemEnv) (δ : TySubst) (γ : TmSubst) : Prop where
  /-- Every type variable in the context maps to a valid Reducibility Candidate -/
  ty_rel {X} : (X, .ty) ∈ Γ → RC (ρ.free X) ∧ LcTy (δ X)

  /-- Every term variable in the context maps to a term inside the interpreted set -/
  tm_rel {x T} : (x, .tm T) ∈ Γ → γ x ∈ T.interp ρ

  /-- The type substitution is locally closed -/
  δ_lc : ∀ X, LcTy (δ X)

  /-- The term substitution is locally closed -/
  γ_lc : ∀ x, LcTm (γ x)

lemma sn_of_sn_open {t u : Tm} (hu : LcTm u) (h : SN (t⟪u⟫)) : SN t := by
  generalize hEq : t⟪u⟫ = tu at h
  induction h generalizing t u with subst hEq
  | intro x h ih =>
    constructor
    intro t' hStep
    have : t⟪u⟫ ⟶ t'⟪u⟫ := step_openTm hStep 0 u hu
    apply ih _ this hu rfl

lemma RC_app_lam {A t u S}
    (hRC : RC S)
    (hSN : SN u)
    (hLc : LcTm u)
    (hLc_lam : LcTm (ƛ A => t))
    (hBody : t⟪u⟫ ∈ S) :
    (ƛ A => t) ◦ u ∈ S := by
  induction hSN generalizing t with
  | intro x _ ih_x =>
    have := hRC.cr₁ hBody
    have := sn_of_sn_open hLc this
    induction this generalizing x with
    | intro y _ ih_y =>
      apply hRC.cr₃
      · constructor <;> assumption
      · constructor
      · intro v hStep
        cases hStep with
        | app₁ h' =>
          cases h' with
          | @lamBody _ _ y' h'' =>
            have : y⟪x⟫ ⟶ y'⟪x⟫ := step_openTm h'' 0 x hLc
            have : y'⟪x⟫ ∈ S := hRC.cr₂ hBody this
            have : SN (y'⟪x⟫) := hRC.cr₁ this
            apply ih_y _ h'' _ _ _ hLc (lcTm_step hLc_lam _)
            · assumption
            · assumption
            · assumption
            · exact ih_x
            · constructor
              assumption
        | @app₂ _ _ x' h'' =>
          have : y⟪x⟫ ⟶* y⟪x'⟫ := multi_step_openTm h''
          have : y⟪x'⟫ ∈ S := hRC.cr₂_multi hBody this
          apply ih_x
          · assumption
          · exact lcTm_step hLc h''
          · assumption
          · assumption
        | appLam _ _ => assumption

theorem fundamental {Γ t T} (hTyp : Γ ⊢ t ∶ T) {ρ δ γ}
    (hValid : ρ.IsValid) (hEnv : EnvRel Γ ρ δ γ) :
    t.psubst γ δ ∈ T.interp ρ := by
  induction hTyp generalizing ρ δ γ with
  | var Γ x T _ _ _ =>
    simp only [Tm.psubst]
    apply hEnv.tm_rel
    assumption
  | lam L Γ T₁ T₂ t _ h ih =>
    simp only [Ty.interp, arr_set, Tm.psubst, Set.mem_setOf_eq]
    intro u hu
    apply RC_app_lam (interp_soundness T₂ _)
    · apply (interp_soundness T₁ _).cr₁ hu
      assumption
    · exact interp_soundness T₁ hValid |>.lc hu
    · apply LcTm.lam (L ∪ t.fv)
      · apply psubst_lcTy
        · assumption
        · exact hEnv.δ_lc
      · intro x hx
        rw [psubst_openTm_comm (by aesop) (hEnv.γ_lc)]
        apply psubst_lcTm
        · exact h x (by aesop) |> typing_regularity_tm
        · intro y
          by_cases hy : y = x
          · simp [Function.update, hy]
            constructor
          · simp only [Function.update, hy, ↓reduceDIte]
            exact hEnv.γ_lc y
        · exact hEnv.δ_lc
    · have ⟨x, hx⟩ := exists_fresh_name (L ∪ t.fv)
      let γ' := Function.update γ x u
      have hEnv' : EnvRel ((x, .tm T₁) :: Γ) ρ δ γ' := by
        constructor
        · intro Y hY
          simp only [List.mem_cons, Prod.mk.injEq, reduceCtorEq, and_false, false_or] at hY
          exact hEnv.ty_rel hY
        · intro y U hy
          by_cases hxy : y = x
          · simp [hxy, γ']
            have := h x (by aesop) |> typing_regularity_wf
            subst hxy
            have := wf_lookup_mid (Γ₁ := []) (b₂ := .tm U) this (by aesop)
            aesop
          · simp only [ne_eq, hxy, not_false_eq_true, Function.update_of_ne, γ']
            apply hEnv.tm_rel
            aesop
        · exact hEnv.δ_lc
        · intro y
          by_cases hy : y = x
          · simp only [hy, Function.update_self, γ']
            have := interp_soundness T₁ hValid
            exact this.lc hu
          · simp only [ne_eq, hy, not_false_eq_true, Function.update_of_ne, γ']
            apply hEnv.γ_lc
      have := ih x (by aesop) hValid hEnv'
      rw [←psubst_openTm_comm'] at this
      · assumption
      · aesop
      · exact hEnv.γ_lc
    · assumption
  | app Γ t₁ t₂ T₁ T₂ _ _ _ _ => sorry
  | tLam L Γ t T _ _ => sorry
  | tApp Γ t T₁ T₂ _ _ _ => sorry

end SystemF.StronglyNormalization

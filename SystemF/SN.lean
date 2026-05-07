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
  | tApp₁ {T t t'} : Step t t' → Step (t⦃T⦄) (t'⦃T⦄)
  | tLamBody {t t'} (L : Finset Name) :
      (∀ X, X ∉ L → Step (t⟪$TX⟫) (t'⟪$TX⟫)) → Step (Λ' t) (Λ' t')
  | lamBody {T t t'} (L : Finset Name) :
      LcTy T → (∀ x ∉ L, Step (t⟪$vx⟫) (t'⟪$vx⟫)) → Step (ƛ T => t) (ƛ T => t')
  | appLam {T t₁ t₂} : LcTm (ƛ T => t₁) → LcTm t₂ → Step ((ƛ T => t₁) ◦ t₂) (t₁⟪t₂⟫)
  | tAppTLam {T t} : LcTm (Λ' t) → LcTy T → Step ((Λ' t)⦃T⦄) (t⟪T⟫)

scoped infix:50 " ⟶ " => Step
scoped infix:50 " ⟶* " => Relation.ReflTransGen Step

abbrev BackwardsStep := flip Step

scoped infix:50 " ⟵ " => BackwardsStep
scoped infix:50 " *⟵ " => Relation.ReflTransGen BackwardsStep

@[simp]
lemma step_of_backwards_step {t t' : Tm} : (t ⟵ t') = (t' ⟶ t) := rfl

theorem lcTm_step {t t' : Tm} (h : LcTm t) (hStep : t ⟶ t') : LcTm t' := by
  induction hStep with
  | app₁ _ _ => cases h; constructor <;> aesop
  | app₂ _ _ => cases h; constructor <;> aesop
  | tApp₁ _ _ => cases h; constructor <;> aesop
  | tLamBody L _ ih =>
    cases h with
    | tLam L' t h => apply_cofinite; grind
  | lamBody L _ _ ih =>
    cases h with
    | lam L' T t _ h =>
      apply_cofinite <;> grind
  | appLam _ _ => cases h; grind
  | tAppTLam _ _ => cases h; grind

theorem lcTm_multi_step {t t' : Tm} (h : LcTm t) (hSteps : t ⟶* t') : LcTm t' := by
  induction hSteps with
  | refl => assumption
  | tail _ hStep ih => apply lcTm_step ih hStep

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

lemma Step.multi_app₁ {t₁ t₁' t₂ : Tm} (h : t₁ ⟶* t₁') :
    (t₁ ◦ t₂) ⟶* (t₁' ◦ t₂) := by
  induction h with
  | refl => rfl
  | tail _ hStep ih => exact Relation.ReflTransGen.tail ih (Step.app₁ hStep)

lemma Step.multi_app₂ {t₁ t₂ t₂' : Tm} (h : t₂ ⟶* t₂') :
    (t₁ ◦ t₂) ⟶* (t₁ ◦ t₂') := by
  induction h with
  | refl => rfl
  | tail _ hStep ih => exact Relation.ReflTransGen.tail ih (Step.app₂ hStep)

lemma Step.multi_tApp {t t' : Tm} {T : Ty} (h : t ⟶* t') :
    (t⦃T⦄) ⟶* (t'⦃T⦄) := by
  induction h with
  | refl => rfl
  | tail _ hStep ih => exact Relation.ReflTransGen.tail ih (Step.tApp₁ hStep)

lemma step_substTm {t t' u : Tm} {x : Name}
    (hStep : t ⟶ t')
    (hu : LcTm u) :
    (t[x ↦ u]) ⟶ (t'[x ↦ u]) := by
  induction hStep generalizing u with
  | app₁ _ _ => simp only [substTm_app]; apply Step.app₁; aesop
  | app₂ _ _ => simp only [substTm_app]; apply Step.app₂; aesop
  | tApp₁ _ _ => simp only [substTm_tApp]; apply Step.tApp₁; aesop
  | tLamBody L _ ih =>
    simp only [substTm_tLam]
    apply Step.tLamBody L
    intro Y hY
    simp only [← openTmTy_substTm_comm hu]
    apply ih
    · assumption
    · assumption
  | lamBody L hT _ ih =>
    simp only [substTm_lam]
    apply Step.lamBody (L ∪ {x}) hT
    intro y hy
    rw [openTm_substTm_comm_of_neq (by aesop) hu]
    rw [openTm_substTm_comm_of_neq (by aesop) hu]
    apply ih
    · aesop
    · assumption
  | appLam h _ =>
    simp only [substTm_app, substTm_lam]
    rw [←openTm_substTm_comm hu]
    apply Step.appLam
    · rw [←substTm_lam]
      apply substTm_lcTm
      · assumption
      · assumption
    · apply substTm_lcTm
      · assumption
      · assumption
  | tAppTLam _ _ =>
    simp only [substTm_tApp, substTm_tLam]
    rw [openTmTy_substTm_comm hu]
    apply Step.tAppTLam
    · rw [←substTm_tLam]
      apply substTm_lcTm
      · assumption
      · assumption
    · assumption

lemma step_substTmTy {t t' : Tm} {X : Name} {U : Ty}
    (hStep : t ⟶ t')
    (hU : LcTy U) :
    (t[X ↦ U]) ⟶ (t'[X ↦ U]) := by
  induction hStep generalizing U with
  | app₁ _ _ => simp only [substTmTy_app]; apply Step.app₁; aesop
  | app₂ _ _ => simp only [substTmTy_app]; apply Step.app₂; aesop
  | tApp₁ _ _ => simp only [substTmTy_tApp]; apply Step.tApp₁; aesop
  | @tLamBody t t' L _ ih =>
    apply Step.tLamBody (L ∪ {X})
    intro Y hY
    -- substTmTy X U t✝⟪$TY⟫ ⟶ substTmTy X U t'✝⟪$TY⟫
    change (t[X ↦ U])⟪$TY⟫ ⟶ (t'[X ↦ U])⟪$TY⟫
    rw [openTmTy_substTmTy_comm (by aesop) hU]
    rw [openTmTy_substTmTy_comm (by aesop) hU]
    apply ih
    · aesop
    · assumption
  | @lamBody _ t t' L _ _ ih =>
    apply Step.lamBody (L ∪ {X})
    · apply substTy_lcTy
      · assumption
      · assumption
    · intro y hy
      change (t[X ↦ U])⟪$vy⟫ ⟶ (t'[X ↦ U])⟪$vy⟫
      rw [openTm_substTmTy_comm_fresh (by aesop)]
      rw [openTm_substTmTy_comm_fresh (by aesop)]
      apply ih
      · aesop
      · assumption
  | appLam _ _ =>
    simp only [substTmTy_app, substTmTy_lam]
    rw [←openTm_substTmTy_comm]
    apply Step.appLam
    · rw [←substTmTy_lam]
      apply substTmTy_lcTm
      · assumption
      · assumption
    · apply substTmTy_lcTm
      · assumption
      · assumption
  | tAppTLam _ _ =>
    simp only [substTmTy_tApp, substTmTy_tLam]
    rw [←openTmTy_substTmTy_comm' hU]
    apply Step.tAppTLam
    · rw [←substTmTy_tLam]
      apply substTmTy_lcTm
      · assumption
      · assumption
    · apply substTy_lcTy
      · assumption
      · assumption

lemma step_lamBody_openTm
    {L : Finset Name} {t t' u : Tm}
    (hBody : ∀ x ∉ L, (t⟪$vx⟫) ⟶ (t'⟪$vx⟫))
    (hu : LcTm u) :
    (t⟪u⟫) ⟶ (t'⟪u⟫) := by
  obtain ⟨x, hx⟩ := exists_fresh_name (L ∪ t.fv ∪ t'.fv)
  have := hBody x (by aesop)
  have := step_substTm (x := x) this hu
  rw [substTm_openTm_var (by aesop)] at this
  rw [substTm_openTm_var (by aesop)] at this
  exact this

lemma step_tLamBody_openTmTy
    {L : Finset Name} {t t' : Tm} {U : Ty}
    (hBody : ∀ X ∉ L, (t⟪$TX⟫) ⟶ (t'⟪$TX⟫))
    (hU : LcTy U) :
    (t⟪U⟫) ⟶ (t'⟪U⟫) := by
  obtain ⟨X, hX⟩ := exists_fresh_name (L ∪ t.fvTy ∪ t'.fvTy)
  have := hBody X (by aesop)
  have := step_substTmTy (X := X) this hU
  rw [substTmTy_openTmTy_var (by aesop)] at this
  rw [substTmTy_openTmTy_var (by aesop)] at this
  exact this

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

lemma sn_of_sn_tApp {t : Tm} {T : Ty} (h : SN (t⦃T⦄)) : SN t := by
  generalize hEq : t⦃T⦄ = tT at h
  induction h generalizing t with subst hEq
  | intro x h ih =>
    constructor
    intro t' hStep
    have : (t⦃T⦄) ⟶ (t'⦃T⦄) := Step.tApp₁ hStep
    exact ih _ this rfl

def all_set (F : Set Tm → Set Tm) : Set Tm := { t | ∀ S, RC S → ∀ U, LcTy U → t⦃U⦄ ∈ F S }

scoped notation "∀' " F => all_set F

theorem RC_all {F : Set Tm → Set Tm} (hF : ∀ S, RC S → RC (F S)) : RC (∀' F) := by
  constructor
  · intro t ht
    let T := $T"dummy"
    have : LcTy T := by constructor
    have : t⦃T⦄ ∈ F sn_set := ht _ RC_sn _ this
    have := hF sn_set RC_sn |>.lc this
    cases this
    assumption
  · intro t ht
    let T := $T"dummy"
    have : LcTy T := by constructor
    have : t⦃T⦄ ∈ F sn_set := ht _ RC_sn _ this
    have := hF sn_set RC_sn |>.cr₁ this
    apply sn_of_sn_tApp
    assumption
  · intro t t' ht hStep S hS U hU
    exact hF S hS |>.cr₂ (ht S hS U hU) (Step.tApp₁ hStep)
  · intro t hLc hNeu h S hS U hU
    apply hF S hS |>.cr₃
    · constructor <;> assumption
    · constructor
    · intro t' hStep
      cases hStep with
      | tApp₁ hStep =>
        exact h _ hStep S hS U hU
      | tAppTLam _ _ => cases hNeu

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

@[simp]
lemma envRel_empty : EnvRel [] SemEnv.empty TySubst.empty TmSubst.empty := by
  constructor <;> simp [SemEnv.empty, TySubst.empty, TmSubst.empty] <;> try intro; constructor

lemma sn_lam_of_sn_open {A} {t u : Tm} (hLc_u : LcTm u) (h : SN (t⟪u⟫)) : SN (ƛ A => t) := by
  generalize hEq : t⟪u⟫ = tu at h
  induction h generalizing t with subst hEq
  | intro tu _ ih =>
    constructor
    intro v hStep
    cases hStep with
    | @lamBody T t t' L hLc_T hStepBody =>
      have hStepOpen : t⟪u⟫ ⟶ t'⟪u⟫ := step_lamBody_openTm hStepBody hLc_u
      exact ih _ hStepOpen rfl

lemma RC_app_lam {A t u S}
    (hRC : RC S)
    (hSN_u : SN u)
    (hLc_u : LcTm u)
    (hLc_lam : LcTm (ƛ A => t))
    (hBody : ∀ u', u ⟶* u' → t⟪u'⟫ ∈ S) :
    (ƛ A => t) ◦ u ∈ S := by
  have h_tu : t⟪u⟫ ∈ S := hBody _ (by rfl)
  have hSN_lam : SN (ƛ A => t) := sn_lam_of_sn_open hLc_u (hRC.cr₁ h_tu)
  generalize hEq : (ƛ A => t) = lam at hSN_lam
  induction hSN_lam generalizing t u with
  | intro lam _ ih_lam =>
    induction hSN_u generalizing t with subst hEq
    | intro u h ih_u =>
      apply hRC.cr₃
      · constructor <;> assumption
      · constructor
      · intro v hStep
        cases hStep with
        | app₁ hStepFunc =>
          cases hStepFunc with
          | @lamBody _ t t' L hLc_T hStepBody =>
            have hLc_lam' : LcTm (ƛ A => t') :=
              lcTm_step hLc_lam (Step.lamBody L hLc_T hStepBody)
            have hBody' : ∀ u', u ⟶* u' → t'⟪u'⟫ ∈ S := by
              intro u' hSteps
              have hLc_u' : LcTm u' := lcTm_multi_step hLc_u hSteps
              have hStepOpen' : t⟪u'⟫ ⟶ t'⟪u'⟫ := step_lamBody_openTm hStepBody hLc_u'
              exact hRC.cr₂ (hBody u' hSteps) hStepOpen'
            have hSN_u : SN u := Acc.intro u h
            have : (ƛ A => t) ⟶ (ƛ A => t') := Step.lamBody L hLc_T hStepBody
            exact ih_lam
              _
              this
              hSN_u
              hLc_u
              hLc_lam'
              hBody'
              (hBody' _ (by rfl))
              rfl
        | @app₂ _ u u' hStep =>
          have hLc_u' : LcTm u' := lcTm_step hLc_u hStep
          have hBody' : ∀ u'', u' ⟶* u'' → t⟪u''⟫ ∈ S := by
            intro u'' hSteps
            exact hBody u'' (Relation.ReflTransGen.head hStep hSteps)
          exact ih_u _ hStep hLc_u' hLc_lam hBody' (hBody' _ (by rfl)) rfl
        | appLam _ _ => apply hBody; rfl

lemma sn_tLam_of_sn_open {t : Tm} {U : Ty} (hLc_U : LcTy U) (h : SN (t⟪U⟫)) : SN (Λ' t) := by
  generalize hEq : t⟪U⟫ = tU at h
  induction h generalizing t with
  | intro tU _ ih =>
    subst hEq
    constructor
    intro v hStep
    cases hStep with
    | @tLamBody t t' L hStepBody =>
      have hStepOpen : t⟪U⟫ ⟶ t'⟪U⟫ := step_tLamBody_openTmTy hStepBody hLc_U
      exact ih _ hStepOpen rfl

lemma RC_tApp_tLam {t U S}
    (hRC : RC S)
    (hLc_tLam : LcTm (Λ' t))
    (hLc_U : LcTy U)
    (hBody : t⟪U⟫ ∈ S) :
    (Λ' t)⦃U⦄ ∈ S := by
  have hSN_tLam : SN (Λ' t) := sn_tLam_of_sn_open hLc_U (hRC.cr₁ hBody)
  generalize hEq : (Λ' t) = tLam at hSN_tLam
  induction hSN_tLam generalizing t with subst hEq
  | intro x h ih =>
    apply hRC.cr₃
    · constructor <;> assumption
    · constructor
    · intro v hStep
      cases hStep with
      | tApp₁ hStep =>
        cases hStep with
        | @tLamBody t t' L hStepBody =>
          have hStepOpen : t⟪U⟫ ⟶ t'⟪U⟫ := step_tLamBody_openTmTy hStepBody hLc_U
          have hLc_tLam' : LcTm (Λ' t') := lcTm_step hLc_tLam (Step.tLamBody L hStepBody)
          have ht'_in_S : t'⟪U⟫ ∈ S := hRC.cr₂ hBody hStepOpen
          have := Step.tLamBody L hStepBody
          exact ih _ this hLc_tLam' ht'_in_S rfl
      | tAppTLam _ _ => exact hBody

lemma interp_openTy_comm_at {T : Ty} {k : ℕ} {X : Name} {ρ : SemEnv} {S : Set Tm}
    (hX : X ∉ T.fv)
    (hk : k ≤ ρ.bound.length)
    (hLcT : T.LcAt (k + 1)) :
    T.interp { ρ with bound := ρ.bound.insertIdx k S } =
    (T⟪k, $TX⟫).interp { ρ with free := Function.update ρ.free X S } := by
  induction T generalizing ρ k with
  | bvar idx =>
    simp [Ty.LcAt] at hLcT
    rcases Nat.lt_trichotomy idx k with (hlt | heq | hgt)
    · have h₁ : idx ≠ k := by aesop
      simp [Ty.interp, h₁]
      grind
    · simp [Ty.interp, heq]
      grind
    · simp [Ty.interp]
      grind
  | fvar name =>
    simp only [Ty.fv, Finset.mem_singleton, openTy_fvar] at *
    have : name ≠ X := by aesop
    simp [Ty.interp, this]
  | arr T₁ T₂ T₁_ih T₂_ih =>
    simp only [Ty.interp, openTy_arr]
    simp only [Ty.fv, Finset.mem_union, not_or] at hX
    simp only [Ty.LcAt] at hLcT
    aesop
  | all T ih =>
    simp only [Ty.LcAt] at hLcT
    simp only [Ty.fv] at hX
    simp only [Ty.interp, openTy_all]
    funext t
    congr
    funext S'
    exact ih (ρ := { bound := S' :: ρ.bound, free := ρ.free }) hX (by grind) hLcT

lemma List.insertIdx_cons {α} (xs : List α) (x : α) : List.insertIdx xs 0 x = x :: xs := rfl

lemma interp_openTy_fvar {T : Ty} {X : Name} {ρ : SemEnv} {S : Set Tm}
    (hX : X ∉ T.fv) (hLcT : T.LcAt 1) :
    T.interp { ρ with bound := S :: ρ.bound } =
    (T⟪$T X⟫).interp { ρ with free := Function.update ρ.free X S } := by
  rw [←List.insertIdx_cons]
  apply interp_openTy_comm_at hX (by simp) hLcT

lemma interp_bound_irr_at {T : Ty} {k : ℕ} {ρ : SemEnv} {S : Set Tm}
    (hk : k ≤ ρ.bound.length)
    (hLc : T.LcAt k) :
    T.interp { ρ with bound := ρ.bound.insertIdx k S } = T.interp ρ := by
  induction T generalizing ρ k with
  | bvar idx =>
    simp [Ty.LcAt] at hLc
    rcases Nat.lt_trichotomy idx k with (hlt | heq | hgt)
    · simp [Ty.interp]
      grind
    · simp [Ty.interp]
      grind
    · simp [Ty.interp]
      grind
  | fvar name => simp [Ty.interp]
  | arr T₁ T₂ T₁_ih T₂_ih =>
    simp [Ty.LcAt] at hLc
    simp [Ty.interp, T₁_ih hk hLc.1, T₂_ih hk hLc.2]
  | all T ih =>
    simp only [Ty.LcAt] at hLc
    simp only [Ty.interp]
    funext t
    congr
    funext S'
    exact ih (ρ := { bound := S' :: ρ.bound, free := ρ.free }) (by grind) hLc

lemma interp_bound_irr {T : Ty} {ρ : SemEnv} {S : Set Tm} (hLc : T.LcAt 0) :
    T.interp { ρ with bound := S :: ρ.bound } = T.interp ρ := by
  rw [←List.insertIdx_cons]
  apply interp_bound_irr_at (by simp) hLc

lemma interp_openTy_bound_at {T U : Ty} {k : ℕ} {ρ : SemEnv}
    (hk : k ≤ ρ.bound.length)
    (hLcT : T.LcAt (k + 1))
    (hLcU : U.LcAt 0) :
    T.interp { ρ with bound := ρ.bound.insertIdx k (U.interp ρ) } =
    (T⟪k, U⟫).interp ρ := by
  induction T generalizing ρ k with
  | bvar idx =>
    simp [Ty.LcAt] at hLcT
    rcases Nat.lt_trichotomy idx k with (hlt | heq | hgt)
    · have h₁ : idx ≠ k := by aesop
      simp [Ty.interp, h₁]
      grind
    · simp [Ty.interp, heq]
      grind
    · simp [Ty.interp]
      grind
  | fvar name => simp [Ty.interp]
  | arr T₁ T₂ T₁_ih T₂_ih =>
    simp [Ty.LcAt] at hLcT
    simp [Ty.interp, openTy_arr, T₁_ih hk hLcT.1, T₂_ih hk hLcT.2]
  | all T ih =>
    simp only [Ty.LcAt] at hLcT
    simp only [Ty.interp, openTy_all]
    funext t
    congr
    funext S'
    have := ih (ρ := { bound := S' :: ρ.bound, free := ρ.free }) (k := k + 1) (by grind) hLcT
    simp only [interp_bound_irr hLcU, List.insertIdx_succ_cons] at this
    exact this

lemma interp_openTy_bound {T U : Ty} {ρ : SemEnv} (hLcT : T.LcAt 1) (hLcU : U.LcAt 0) :
    T.interp { ρ with bound := (U.interp ρ) :: ρ.bound } =
    (T⟪U⟫).interp ρ := by
  rw [←List.insertIdx_cons]
  apply interp_openTy_bound_at (by simp) hLcT hLcU

lemma interp_free_update_of_not_mem {T : Ty} {X : Name} {ρ : SemEnv} {S : Set Tm}
    (hX : X ∉ T.fv) :
    T.interp { ρ with free := Function.update ρ.free X S } = T.interp ρ := by
  induction T generalizing ρ with
  | bvar idx => rfl
  | fvar name =>
    simp at hX
    simp only [Ty.interp, Function.update, eq_rec_constant, dite_eq_ite, ite_eq_right_iff]
    intro _
    aesop
  | arr T₁ T₂ T₁_ih T₂_ih =>
    simp at hX
    simp [Ty.interp, T₁_ih hX.1, T₂_ih hX.2]
  | all T ih =>
    simp only [Ty.fv] at hX
    simp only [Ty.interp]
    funext T
    congr
    funext S'
    exact ih (ρ := { bound := S' :: ρ.bound, free := ρ.free }) hX

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
    · apply_cofinite
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
    · intro u' hSteps
      have hRC₁ := interp_soundness T₁ hValid
      have hu' : u' ∈ T₁.interp ρ := hRC₁.cr₂_multi hu hSteps
      obtain ⟨x, hx⟩ := exists_fresh_name (L ∪ t.fv)
      let γ' := Function.update γ x u'
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
            exact this.lc hu'
          · simp only [ne_eq, hy, not_false_eq_true, Function.update_of_ne, γ']
            apply hEnv.γ_lc
      have := ih x (by aesop) hValid hEnv'
      rw [←psubst_openTm_comm'] at this
      · assumption
      · aesop
      · exact hEnv.γ_lc
    · assumption
  | app Γ t₁ t₂ T₁ T₂ _ _ ih₁ ih₂ =>
    simp only [Tm.psubst]
    have h₁ := ih₁ hValid hEnv
    have h₂ := ih₂ hValid hEnv
    exact h₁ _ h₂
  | tLam L Γ t T h ih =>
    simp only [Ty.interp, all_set, Tm.psubst, Set.mem_setOf_eq]
    intro S hS U hLc_U
    obtain ⟨X, hX⟩ := exists_fresh_name (L ∪ T.fv ∪ t.fvTy ∪ Context.fv Γ)
    let δ' := Function.update δ X U
    let ρ' := { ρ with free := Function.update ρ.free X S }
    have hEnv' : EnvRel ((X, Binding.ty) :: Γ) ρ' δ' γ := by
      constructor
      · intro Y hY
        simp only [List.mem_cons, Prod.mk.injEq, and_true] at hY
        by_cases hXY : Y = X
        · simp only [Function.update, hXY, ↓reduceDIte, eq_rec_constant, Function.update_self, δ',
          ρ']
          exact ⟨hS, hLc_U⟩
        · simp only [Finset.union_assoc, Finset.mem_union, not_or, hXY, false_or,
          not_false_eq_true, ne_eq, Function.update_of_ne, δ', ρ'] at *
          exact hEnv.ty_rel hY
      · intro y U hy
        simp only [List.mem_cons] at hy
        cases hy with
        | inl h => cases h
        | inr h =>
          have := hEnv.tm_rel h
          have := subset_fv_of_mem_tm h
          have : U.interp ρ' = U.interp ρ := interp_free_update_of_not_mem (by grind)
          simpa [this]
      · intro Y
        by_cases hXY : Y = X
        · simp only [hXY, Function.update_self, δ']
          exact hLc_U
        · simp only [ne_eq, hXY, not_false_eq_true, Function.update_of_ne, δ']
          apply hEnv.δ_lc
      · exact hEnv.γ_lc
    have hValid' : ρ'.IsValid := by
      constructor
      · intro Y
        by_cases hXY : Y = X
        · simp [ρ', hXY, Function.update, hS]
        · simp only [ne_eq, hXY, not_false_eq_true, Function.update_of_ne, ρ']
          exact hValid.free_rc Y
      · exact hValid.bound_rc
    have := ih X (by aesop) hValid' hEnv'
    have hLcAt_t : T.LcAt 1 := by
      have := h X (by aesop) |> typing_regularity_ty
      have := lcAt_zero_of_lcTy this
      have := lcAtTy_of_openTy this
      simp [this]
    rw [←psubst_openTmTy_comm' (by aesop) (hEnv.γ_lc) (hEnv.δ_lc)] at this
    rw [←interp_openTy_fvar (by aesop) hLcAt_t] at this
    apply RC_tApp_tLam
    · apply interp_soundness
      apply semEnv_valid_extend_bound hValid hS
    · apply LcTm.tLam (L ∪ t.fvTy)
      intro Y hY
      rw [psubst_openTmTy_comm (by aesop) (hEnv.γ_lc) (hEnv.δ_lc)]
      apply psubst_lcTm
      · have := h Y (by aesop) |> typing_regularity_tm
        apply this
      · exact hEnv.γ_lc
      · intro Y'
        by_cases hYY' : Y' = Y
        · simp [hYY', Function.update]
          constructor
        · simp only [Function.update, hYY', ↓reduceDIte]
          apply hEnv.δ_lc
    · exact hLc_U
    · exact this
  | tApp Γ t T₁ T₂ h _ ih =>
    simp only [Tm.psubst]
    have f := ih hValid hEnv
    simp only [Ty.interp, all_set, Set.mem_setOf_eq] at f
    have hLc_subst_T₂ : LcTy (T₂.psubst δ) := by
      apply psubst_lcTy
      · assumption
      · exact hEnv.δ_lc
    have hRC_T₂ := interp_soundness T₂ hValid
    have := f (T₂.interp ρ) hRC_T₂ _ hLc_subst_T₂
    have hLc_all : LcTy (∀' T₁) := typing_regularity_ty h
    have hLc_T₁ : T₁.LcAt 1 := by
      cases hLc_all with
      | all L T h =>
        obtain ⟨X, hX⟩ := exists_fresh_name L
        have := h X hX
        apply lcAtTy_of_openTy
        apply lcAt_zero_of_lcTy this
    rw [interp_openTy_bound hLc_T₁ (lcAt_zero_of_lcTy (by assumption))] at this
    exact this

theorem strongly_normalizing {t T} (hTyp : ∅ ⊢ t ∶ T) : SN t := by
  have := fundamental hTyp semEnv_empty_valid envRel_empty
  simp only [tm_psubst_id] at this
  have hRC_T := interp_soundness T semEnv_empty_valid
  apply hRC_T.cr₁ this

end SystemF.StronglyNormalization

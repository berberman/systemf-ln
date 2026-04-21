import SystemF.Metatheory

namespace SystemF

abbrev TmRel := Tm → Tm → Prop

structure IsValCandidateRel (R : TmRel) : Prop where
  val_left {t₁ t₂} : R t₁ t₂ → Value t₁
  val_right {t₁ t₂} : R t₁ t₂ → Value t₂
  lc_left {t₁ t₂} : R t₁ t₂ → LcTm t₁
  lc_right {t₁ t₂} : R t₁ t₂ → LcTm t₂

abbrev SemEnv := List TmRel

/-- A dummy closed type for defining `ValRel` -/
def Ty.dummy : Ty := .all (.bvar 0)

theorem ty_dummy_lc : LcTy Ty.dummy := by
  apply LcTy.all ∅
  intros
  constructor

mutual

/-- `ℰ[T]`: two terms are related if they can both evaluate to
  values that are related by the value relation.
  Here `VRel` is parameterized to avoid mutual recursion. -/
def ExpRel (T : Ty) (ρ : SemEnv) : TmRel :=
  fun t₁ t₂ =>
    LcTm t₁ ∧ LcTm t₂ ∧
    ∃ v₁ v₂, (t₁ ⟶* v₁) ∧ (t₂ ⟶* v₂) ∧ ValRel T ρ v₁ v₂

/-- `𝒱[T]`: two terms are related if they are both values and
  if they are functions, applying the them yields related expressions -/
def ValRel (T : Ty) (ρ : SemEnv) : TmRel :=
  match T with
  | .bvar idx => if h : idx < ρ.length then ρ[idx] else fun _ _ => False
  | .fvar name => fun _ _ => False
  | .arr T₁ T₂ =>
    fun v₁ v₂ =>
      Value v₁ ∧ Value v₂ ∧ LcTm v₁ ∧ LcTm v₂ ∧
      (∃ body₁, v₁ = (ƛ T₁ => body₁)) ∧
      (∃ body₂, v₂ = (ƛ T₁ => body₂)) ∧
      ∀ arg₁ arg₂, ValRel T₁ ρ arg₁ arg₂ → ExpRel T₂ ρ (v₁ ◦ arg₁) (v₂ ◦ arg₂)
  | .all T =>
    fun v₁ v₂ =>
      Value v₁ ∧ Value v₂ ∧ LcTm v₁ ∧ LcTm v₂ ∧
      (∃ body₁, v₁ = (Λ' body₁)) ∧
      (∃ body₂, v₂ = (Λ' body₂)) ∧
      ∀ R, IsValCandidateRel R → ExpRel T (R :: ρ) (v₁⦃Ty.dummy⦄) (v₂⦃Ty.dummy⦄)

end

def SemEnv.IsValid (ρ : SemEnv) : Prop :=
  ∀ R ∈ ρ, IsValCandidateRel R

@[simp]
theorem false_candidate : IsValCandidateRel (fun _ _ => False) := by
  constructor <;> simp

@[simp]
theorem valRel_candidate {T : Ty} {ρ : SemEnv} (hValid : ρ.IsValid) :
    IsValCandidateRel (ValRel T ρ) := by
  induction T generalizing ρ with
  | bvar idx =>
    simp [ValRel]
    by_cases h : idx < ρ.length
    · aesop
    · simp [h]
  | fvar name => simp [ValRel]
  | arr T₁ T₂ T₁_ih T₂_ih =>
    simp only [ValRel]
    constructor <;> aesop
  | all T ih =>
    simp only [ValRel]
    constructor <;> aesop

lemma expRel_of_valRel {T : Ty} {ρ : SemEnv} {v₁ v₂ : Tm}
    (hValid : ρ.IsValid)
    (hValRel : ValRel T ρ v₁ v₂) : ExpRel T ρ v₁ v₂ := by
  simp only [ExpRel, exists_and_left]
  have : LcTm v₁ := valRel_candidate hValid |>.lc_left hValRel
  have : LcTm v₂ := valRel_candidate hValid |>.lc_right hValRel
  constructor
  · assumption
  · constructor
    · assumption
    · constructor
      · constructor
        · rfl
        · use v₂

lemma expRel_step_back_left {T : Ty} {ρ : SemEnv} {t₁ t₁' t₂ : Tm}
    (hLc_t₁ : LcTm t₁) (hStep : t₁ ⟶ t₁') (hExp : ExpRel T ρ t₁' t₂) : ExpRel T ρ t₁ t₂ := by
  simp only [ExpRel, exists_and_left] at *
  rcases hExp with ⟨hLc_t₁', hLc_t₂, v₁, hEval₁, v₂, hEval₂, hVal⟩
  refine ⟨hLc_t₁, hLc_t₂, ?_⟩
  use v₁
  constructor
  · apply Relation.ReflTransGen.head hStep
    assumption
  · use v₂

lemma expRel_step_back_right {T : Ty} {ρ : SemEnv} {t₂ t₂' t₁ : Tm}
    (hLc_t₂ : LcTm t₂) (hStep : t₂ ⟶ t₂') (hExp : ExpRel T ρ t₁ t₂') : ExpRel T ρ t₁ t₂ := by
  simp only [ExpRel, exists_and_left] at *
  rcases hExp with ⟨hLc_t₁, hLc_t₂', v₁, hEval₁, v₂, hEval₂, hVal⟩
  refine ⟨hLc_t₁, hLc_t₂, ?_⟩
  use v₁
  constructor
  · assumption
  · use v₂
    constructor
    · apply Relation.ReflTransGen.head hStep
      assumption
    · assumption

lemma expRel_app {T₁ T₂ : Ty} {ρ : SemEnv} {t₁ t₂ u₁ u₂ : Tm}
    (ht : ExpRel (T₁ ⇒ T₂) ρ t₁ t₂)
    (hu : ExpRel T₁ ρ u₁ u₂) :
    ExpRel T₂ ρ (t₁ ◦ u₁) (t₂ ◦ u₂) := by
  simp only [ExpRel, exists_and_left] at *
  rcases ht with ⟨hLc_t₁, hLc_t₂, v_t₁, hEval₁, v_t₂, hEval_t₂, hVal⟩
  rcases hu with ⟨hLc_u₁, hLc_u₂, v_u₁, hEval_u₁, v_u₂, hEval_u₂, hVal_u⟩
  simp only [ValRel] at hVal
  rcases hVal with ⟨hv_t₁, hv_t₂, hLc_vt₁, hLc_vt₂, ⟨body₁, rfl⟩, ⟨body₂, rfl⟩, f⟩
  have hExp_app := f v_u₁ v_u₂ hVal_u
  simp only [ExpRel, exists_and_left] at hExp_app
  rcases hExp_app with
    ⟨hLc_app₁, hLc_app₂, v_final₁, hEval_final₁, v_final₂, hEval_final₂, hVal_final⟩
  constructor
  · constructor <;> assumption
  · constructor
    · constructor <;> assumption
    · use v_final₁
      constructor
      · apply Relation.ReflTransGen.trans
        · exact multi_app₁ hEval₁ hLc_u₁
        · apply Relation.ReflTransGen.trans
          · exact multi_app₂ hEval_u₁ hv_t₁
          · exact hEval_final₁
      · use v_final₂
        constructor
        · apply Relation.ReflTransGen.trans
          · exact multi_app₁ hEval_t₂ hLc_u₂
          · apply Relation.ReflTransGen.trans
            · exact multi_app₂ hEval_u₂ hv_t₂
            · exact hEval_final₂
        · exact hVal_final

lemma expRel_lam {T₁ T₂ : Ty} {ρ : SemEnv} {t₁ t₂ : Tm}
    (hLc_t₁ : LcTm (ƛ T₁ => t₁))
    (hLc_t₂ : LcTm (ƛ T₁ => t₂))
    (hValid : ρ.IsValid)
    (hBody : ∀ v₁ v₂, ValRel T₁ ρ v₁ v₂ → ExpRel T₂ ρ (t₁⟪v₁⟫) (t₂⟪v₂⟫)) :
    ExpRel (T₁ ⇒ T₂) ρ (ƛ T₁ => t₁) (ƛ T₁ => t₂) := by
  simp only [ExpRel, exists_and_left]
  refine ⟨hLc_t₁, hLc_t₂, ?_⟩
  use (ƛ T₁ => t₁)
  constructor
  · rfl
  · use (ƛ T₁ => t₂)
    constructor
    · rfl
    · simp only [ValRel, Tm.lam.injEq, true_and, exists_eq']
      constructor
      · constructor
      · constructor
        · constructor
        · constructor
          · assumption
          · constructor
            · assumption
            · intro arg₁ arg₂ hVal
              have hLc_arg₁ := valRel_candidate hValid |>.lc_left hVal
              have hVal_arg₁ := valRel_candidate hValid |>.val_left hVal
              have hLc_arg₂ := valRel_candidate hValid |>.lc_right hVal
              have hVal_arg₂ := valRel_candidate hValid |>.val_right hVal
              apply expRel_step_back_left
              · constructor <;> assumption
              · exact SmallStep.appLam _ _ _ hLc_t₁ hVal_arg₁
              · apply expRel_step_back_right
                · constructor <;> assumption
                · exact SmallStep.appLam _ _ _ hLc_t₂ hVal_arg₂
                apply hBody
                assumption

end SystemF

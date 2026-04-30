import SystemF.Typing
import SystemF.CBV.Semantics

namespace SystemF.CBV

open Notation

abbrev TmRel := Tm → Tm → Prop

structure IsValCandidateRel (R : TmRel) : Prop where
  val_left {t₁ t₂} : R t₁ t₂ → Value t₁
  val_right {t₁ t₂} : R t₁ t₂ → Value t₂
  lc_left {t₁ t₂} : R t₁ t₂ → LcTm t₁
  lc_right {t₁ t₂} : R t₁ t₂ → LcTm t₂

structure SemEnv where
  bound : List TmRel
  free  : Name → TmRel

mutual

/-- `ℰ[T]`: two terms are related if they can both evaluate to
  values that are related by the value relation. -/
def ExpRel (T : Ty) (ρ : SemEnv) : TmRel :=
  fun t₁ t₂ =>
    LcTm t₁ ∧ LcTm t₂ ∧
    ∃ v₁ v₂, (t₁ ⟶* v₁) ∧ (t₂ ⟶* v₂) ∧ ValRel T ρ v₁ v₂

/-- `𝒱[T]`: two terms are related if they are both values and
  if they are functions, applying the them yields related expressions -/
def ValRel (T : Ty) (ρ : SemEnv) : TmRel :=
  match T with
  | .bvar idx => if h : idx < ρ.bound.length then ρ.bound[idx] else fun _ _ => False
  | .fvar name => ρ.free name
  | .arr T₁ T₂ =>
    fun v₁ v₂ =>
      Value v₁ ∧ Value v₂ ∧ LcTm v₁ ∧ LcTm v₂ ∧
      (∃ A₁ body₁, v₁ = (ƛ A₁ => body₁)) ∧
      (∃ A₂ body₂, v₂ = (ƛ A₂ => body₂)) ∧
      ∀ arg₁ arg₂, ValRel T₁ ρ arg₁ arg₂ → ExpRel T₂ ρ (v₁ ◦ arg₁) (v₂ ◦ arg₂)
  | .all T =>
    fun v₁ v₂ =>
      Value v₁ ∧ Value v₂ ∧ LcTm v₁ ∧ LcTm v₂ ∧
      (∃ body₁, v₁ = (Λ' body₁)) ∧
      (∃ body₂, v₂ = (Λ' body₂)) ∧
      ∀ R U₁ U₂, IsValCandidateRel R → LcTy U₁ →
        LcTy U₂ → ExpRel T {ρ with bound := R :: ρ.bound} (v₁⦃U₁⦄) (v₂⦃U₂⦄)

end

def SemEnv.IsValid (ρ : SemEnv) : Prop :=
  (∀ R ∈ ρ.bound, IsValCandidateRel R) ∧ (∀ X, IsValCandidateRel (ρ.free X))

@[simp]
theorem rel_false_candidate : IsValCandidateRel (fun _ _ => False) := by
  constructor <;> simp

def SemEnv.empty : SemEnv := { bound := [], free := fun _ => fun _ _ => False }

@[simp]
theorem semEnv_empty_valid : SemEnv.IsValid SemEnv.empty := by
  constructor <;> simp [SemEnv.empty]

@[simp]
theorem valRel_candidate {T : Ty} {ρ : SemEnv} (hValid : ρ.IsValid) :
    IsValCandidateRel (ValRel T ρ) := by
  induction T generalizing ρ with
  | bvar idx =>
    simp [ValRel]
    by_cases h : idx < ρ.bound.length
    · simp [SemEnv.IsValid] at hValid
      aesop
    · simp [h]
  | fvar name =>
    simp [ValRel]
    simp [SemEnv.IsValid] at hValid
    aesop
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
  rcases hVal with ⟨hv_t₁, hv_t₂, hLc_vt₁, hLc_vt₂, ⟨A₁, body₁⟩, ⟨A₂, body₂⟩, f⟩
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

lemma expRel_lam {T₁ T₂ A₁ A₂ : Ty} {ρ : SemEnv} {t₁ t₂ : Tm}
    (hLc_t₁ : LcTm (ƛ A₁ => t₁))
    (hLc_t₂ : LcTm (ƛ A₂ => t₂))
    (hValid : ρ.IsValid)
    (hBody : ∀ v₁ v₂, ValRel T₁ ρ v₁ v₂ → ExpRel T₂ ρ (t₁⟪v₁⟫) (t₂⟪v₂⟫)) :
    ExpRel (T₁ ⇒ T₂) ρ (ƛ A₁ => t₁) (ƛ A₂ => t₂) := by
  simp only [ExpRel, exists_and_left]
  refine ⟨hLc_t₁, hLc_t₂, ?_⟩
  use (ƛ A₁ => t₁)
  constructor
  · rfl
  · use (ƛ A₂ => t₂)
    constructor
    · rfl
    · simp only [ValRel, Tm.lam.injEq, exists_and_left, ↓existsAndEq, and_true, exists_eq',
      true_and]
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

lemma expRel_tLam {T : Ty} {ρ : SemEnv} {t₁ t₂ : Tm}
    (hLc_t₁ : LcTm (Λ' t₁))
    (hLc_t₂ : LcTm (Λ' t₂))
    (hBody : ∀ R U₁ U₂, IsValCandidateRel R →
      LcTy U₁ → LcTy U₂ →
      ExpRel T { ρ with bound := R :: ρ.bound } ((Λ' t₁)⦃U₁⦄) ((Λ' t₂)⦃U₂⦄)) :
    ExpRel (∀' T) ρ (Λ' t₁) (Λ' t₂) := by
  simp only [ExpRel, exists_and_left]
  refine ⟨hLc_t₁, hLc_t₂, ?_⟩
  use (Λ' t₁)
  constructor
  · rfl
  · use (Λ' t₂)
    constructor
    · rfl
    · simp only [ValRel, Tm.tLam.injEq, exists_eq', true_and]
      constructor
      · constructor
      · constructor
        · constructor
        · constructor
          · assumption
          · constructor
            · assumption
            · apply hBody

lemma expRel_tApp {T T_arg U₁ U₂ : Ty} {ρ : SemEnv} {t₁ t₂ : Tm}
    (hValid : ρ.IsValid)
    (hLc_U₁ : LcTy U₁)
    (hLc_U₂ : LcTy U₂)
    (ht : ExpRel (∀' T) ρ t₁ t₂) :
    ExpRel T { ρ with bound := ValRel T_arg ρ :: ρ.bound } (t₁⦃U₁⦄) (t₂⦃U₂⦄) := by
  simp only [ExpRel, exists_and_left] at *
  rcases ht with ⟨hLc_t₁, hLc_t₂, v₁, hEval₁, v₂, hEval₂, hVal⟩
  simp only [ValRel] at hVal
  rcases hVal with ⟨hv₁, hv₂, hLc_v₁, hLc_v₂, ⟨body₁, rfl⟩, ⟨body₂, rfl⟩, f⟩
  have hExp_tApp := f (ValRel T_arg ρ) U₁ U₂ (valRel_candidate hValid) hLc_U₁ hLc_U₂
  simp only [ExpRel, exists_and_left] at hExp_tApp
  rcases hExp_tApp with
    ⟨hLc_app₁, hLc_app₂, v_final₁, hEval_final₁, v_final₂, hEval_final₂, hVal_final⟩
  constructor
  · constructor <;> assumption
  · constructor
    · constructor <;> assumption
    · use v_final₁
      constructor
      · apply Relation.ReflTransGen.trans
        · exact multi_tApp hEval₁ hLc_U₁
        · exact hEval_final₁
      · use v_final₂
        constructor
        · apply Relation.ReflTransGen.trans
          · exact multi_tApp hEval₂ hLc_U₂
          · exact hEval_final₂
        · exact hVal_final

structure EnvRel (Γ : Context) (ρ : SemEnv) (δ₁ δ₂ : Name → Ty) (γ₁ γ₂ : Name → Tm) : Prop where
  ty_rel {X} : (X, .ty) ∈ Γ →
    IsValCandidateRel (ρ.free X) ∧ LcTy (δ₁ X) ∧ LcTy (δ₂ X)
  tm_rel {x T} : (x, .tm T) ∈ Γ →
    ValRel T ρ (γ₁ x) (γ₂ x)
  δ₁_lc : ∀ X, LcTy (δ₁ X)
  δ₂_lc : ∀ X, LcTy (δ₂ X)
  γ₁_lc : ∀ x, LcTm (γ₁ x)
  γ₂_lc : ∀ x, LcTm (γ₂ x)

def emptyδ : Name → Ty := fun X => $T X
def emptyγ : Name → Tm := fun x => $v x

@[simp]
lemma ty_psubst_id (T : Ty) : T.psubst emptyδ = T := by
  induction T <;> simp [Ty.psubst, emptyδ, *]

@[simp]
lemma tm_psubst_id (t : Tm) : t.psubst emptyγ emptyδ = t := by
  induction t <;> simp [Tm.psubst, emptyγ, *]

@[simp]
theorem envRel_empty : EnvRel [] SemEnv.empty emptyδ emptyδ emptyγ emptyγ := by
  constructor <;> simp [SemEnv.empty, emptyδ, emptyγ] <;> (intro; constructor)

@[simp]
lemma expRel_eq_of_valRel_eq {ρ₁ ρ₂ : SemEnv} {T₁ T₂ : Ty} (h : ValRel T₁ ρ₁ = ValRel T₂ ρ₂) :
    ExpRel T₁ ρ₁ = ExpRel T₂ ρ₂ := by
  funext t₁ t₂
  simp [ExpRel]
  simp [h]

lemma valRel_free_update_of_not_mem {T : Ty} {X : Name} {ρ : SemEnv} {R : TmRel}
    (hX : X ∉ T.fv) :
    ValRel T { ρ with free := Function.update ρ.free X R } = ValRel T ρ := by
  induction T generalizing ρ with
  | bvar idx => simp [ValRel]
  | fvar Y =>
    have : Y ≠ X := by aesop
    simp [ValRel, Function.update, this]
  | arr T₁ T₂ T₁_ih T₂_ih =>
    simp only [ValRel]
    funext v₁ v₂
    have hX₁ : X ∉ T₁.fv := by aesop
    have hX₂ : X ∉ T₂.fv := by aesop
    rw [T₁_ih hX₁]
    have := @T₂_ih ρ hX₂
    have := expRel_eq_of_valRel_eq this
    rw [this]
  | all T ih =>
    simp only [ValRel]
    funext v₁ v₂
    have hX' : X ∉ T.fv := by aesop
    have : ∀ R₁,
        ExpRel T { bound := R₁ :: ρ.bound, free := Function.update ρ.free X R } =
        ExpRel T { bound := R₁ :: ρ.bound, free := ρ.free } := by
      intro R₁
      let ρ' : SemEnv := { bound := R₁ :: ρ.bound, free := ρ.free }
      have := ih (ρ := ρ') hX'
      exact expRel_eq_of_valRel_eq this
    simp [this]

def _root_.SystemF.Ty.LcAt (T : Ty) (k : ℕ) : Prop :=
  match T with
  | .bvar idx => idx < k
  | .fvar _ => True
  | .arr T₁ T₂ => T₁.LcAt k ∧ T₂.LcAt k
  | .all T => T.LcAt (k + 1)

lemma lcAtTy_of_openTy {T : Ty} {X : Name} {k : ℕ}
    (h : (T⟪k, $TX⟫).LcAt k) : T.LcAt (k + 1) := by
  induction T generalizing k with
  | bvar idx =>
    simp only [openTy_bvar, beq_iff_eq, Ty.LcAt, Order.lt_add_one_iff] at *
    by_cases hIdx : idx = k
    · omega
    · simp [hIdx, Ty.LcAt] at h
      omega
  | fvar name => simp [Ty.LcAt]
  | arr T₁ T₂ T₁_ih T₂_ih => simp [Ty.LcAt] at *; aesop
  | all T ih => simp [Ty.LcAt] at *; grind

lemma lcAt_zero_of_lcTy {T : Ty} (h : LcTy T) : T.LcAt 0 := by
  induction h with
  | fvar x => simp [Ty.LcAt]
  | arr T₁ T₂ _ _ _ _ => simp [Ty.LcAt] at *; aesop
  | all L T _ ih =>
    have ⟨X, hX⟩ := exists_fresh_name L
    have := ih X hX
    have := lcAtTy_of_openTy this
    simp only [zero_add, Ty.LcAt] at *
    assumption

lemma valRel_openTy_comm_at {T : Ty} {k : ℕ} {X : Name} {ρ : SemEnv} {R : TmRel}
    (hX : X ∉ T.fv)
    (hk : k ≤ ρ.bound.length)
    (hLcT : T.LcAt (k + 1)) :
    ValRel T { ρ with bound := ρ.bound.insertIdx k R } =
    ValRel (T⟪k, $TX⟫) { ρ with free := Function.update ρ.free X R } := by
  induction T generalizing ρ k with
  | bvar idx =>
    simp only [ValRel, openTy_bvar, beq_iff_eq]
    simp [Ty.LcAt] at hLcT
    rcases Nat.lt_trichotomy idx k with (hlt | heq | hgt)
    · have : idx ≠ k := by aesop
      simp only [this, ↓reduceIte]
      simp only [ValRel]
      grind
    · simp [heq]
      simp [ValRel]
      have : k < (ρ.bound.insertIdx k R).length := by grind
      simp [this]
    · omega
  | fvar name =>
    simp only [Ty.fv, Finset.mem_singleton, openTy_fvar] at *
    have : name ≠ X := by aesop
    simp [ValRel, Function.update, this]
  | arr T₁ T₂ T₁_ih T₂_ih =>
    simp only [Ty.LcAt] at hLcT
    rcases hLcT with ⟨hLcT₁, hLcT₂⟩
    simp at hX
    specialize T₁_ih (by aesop) hk hLcT₁
    specialize T₂_ih (by aesop) hk hLcT₂
    simp only [ValRel, openTy_arr]
    funext v₁ v₂
    congr
    rw [T₁_ih]
    have := expRel_eq_of_valRel_eq T₂_ih
    rw [this]
  | all T ih =>
    simp only [Ty.LcAt] at hLcT
    simp only [Ty.fv] at hX
    simp only [ValRel, openTy_all]
    funext v₁ v₂
    have h_body : ∀ R_arg,
        ExpRel T { bound := R_arg :: ρ.bound.insertIdx k R, free := ρ.free } =
        ExpRel (T⟪k + 1, $TX⟫)
          { bound := R_arg :: ρ.bound, free := Function.update ρ.free X R } := by
      intro R_arg
      let ρ' : SemEnv := { bound := R_arg :: ρ.bound, free := ρ.free }
      have hk' : k + 1 ≤ ρ'.bound.length := by aesop
      have := ih (ρ := ρ') hX hk' hLcT
      apply expRel_eq_of_valRel_eq
      assumption
    simp [h_body]


lemma List.insertIdx_cons {α} (xs : List α) (x : α) : List.insertIdx xs 0 x = x :: xs := rfl

/-- Evaluating an expression under an environment where index 0 is bound to relation `R`
  is equivalent to opening the type syntactically at index 0 with a fresh name `X`,
  and evaluating it under an environment where `X` is mapped to `R`.
-/
lemma expRel_openTy_comm {T : Ty} {X : Name} {ρ : SemEnv} {R : TmRel} {t₁ t₂ : Tm}
    (hX : X ∉ T.fv)
    (hLcT : T.LcAt 1) :
    ExpRel T { ρ with bound := R :: ρ.bound } t₁ t₂ ↔
    ExpRel (T⟪$TX⟫) { ρ with free := Function.update ρ.free X R } t₁ t₂ := by
  have h_val : ValRel T { ρ with bound := R :: ρ.bound } =
               ValRel (T⟪$TX⟫) { ρ with free := Function.update ρ.free X R } := by
    rw [←List.insertIdx_cons]
    exact valRel_openTy_comm_at hX (by simp) hLcT
  rw [expRel_eq_of_valRel_eq h_val]

lemma valRel_bound_irr_at {T : Ty} {k : ℕ} {ρ : SemEnv} {R : TmRel}
    (hk : k ≤ ρ.bound.length)
    (hLc : T.LcAt k) :
    ValRel T { ρ with bound := ρ.bound.insertIdx k R } = ValRel T ρ := by
  induction T generalizing ρ k with
  | bvar idx =>
    simp [Ty.LcAt] at hLc
    simp only [ValRel]
    rcases Nat.lt_trichotomy idx k with (hlt | heq | hgt)
    · have : idx < ρ.bound.length := by grind
      grind
    · aesop
    · grind
  | fvar name => simp [ValRel]
  | arr T₁ T₂ T₁_ih T₂_ih =>
    simp only [ValRel]
    funext v₁ v₂
    congr
    simp only [Ty.LcAt] at hLc
    rcases hLc with ⟨hLcT₁, hLcT₂⟩
    rw [T₁_ih hk hLcT₁]
    have := T₂_ih hk hLcT₂
    rw [expRel_eq_of_valRel_eq this]
  | all T ih =>
    simp only [ValRel]
    funext v₁ v₂
    congr
    simp only [Ty.LcAt] at hLc
    have h_body : ∀ R_arg,
        ExpRel T { bound := R_arg :: ρ.bound.insertIdx k R, free := ρ.free } =
        ExpRel T { bound := R_arg :: ρ.bound, free := ρ.free } := by
      intro R_arg
      let ρ' : SemEnv := { bound := R_arg :: ρ.bound, free := ρ.free }
      have hk' : k + 1 ≤ ρ'.bound.length := by aesop
      have := ih (ρ := ρ') hk' hLc
      apply expRel_eq_of_valRel_eq
      assumption
    simp [h_body]

lemma valRel_bound_irr {T : Ty} {ρ : SemEnv} {R : TmRel} (hLc : T.LcAt 0) :
    ValRel T { ρ with bound := R :: ρ.bound } = ValRel T ρ := by
  rw [←List.insertIdx_cons]
  exact valRel_bound_irr_at (by simp) hLc

lemma valRel_openTy_bound_at {T T_arg : Ty} {k : ℕ} {ρ : SemEnv}
    (hk : k ≤ ρ.bound.length)
    (hLcT : T.LcAt (k + 1))
    (hLcArg : T_arg.LcAt 0) :
    ValRel T { ρ with bound := ρ.bound.insertIdx k (ValRel T_arg ρ) } =
    ValRel (T⟪k, T_arg⟫) ρ := by
  induction T generalizing ρ k with
  | bvar idx =>
    simp [Ty.LcAt] at hLcT
    simp only [ValRel, openTy_bvar, beq_iff_eq]
    rcases Nat.lt_trichotomy idx k with (hlt | heq | hgt)
    · have : idx ≠ k := by grind
      simp only [this, ↓reduceIte]
      have hlt' : idx < ρ.bound.length := by grind
      have hle : idx ≤ ρ.bound.length := by grind
      have h : (ρ.bound.insertIdx k (ValRel T_arg ρ)).length = ρ.bound.length + 1 := by grind
      simp only [h, Order.lt_add_one_iff, hle, ↓reduceDIte]
      rw [List.getElem_insertIdx_of_lt (by assumption) (by grind)]
      simp [ValRel, hlt']
    · grind
    · grind
  | fvar name => simp [ValRel]
  | arr T₁ T₂ T₁_ih T₂_ih =>
    simp only [ValRel, openTy_arr]
    funext v₁ v₂
    congr
    simp only [Ty.LcAt] at hLcT
    rcases hLcT with ⟨hLcT₁, hLcT₂⟩
    rw [T₁_ih hk hLcT₁]
    have := T₂_ih hk hLcT₂
    rw [expRel_eq_of_valRel_eq this]
  | all T ih =>
    simp only [ValRel, openTy_all]
    funext v₁ v₂
    congr
    simp only [Ty.LcAt] at hLcT
    have h_body : ∀ R_arg,
        ExpRel T { bound := R_arg :: ρ.bound.insertIdx k (ValRel T_arg ρ), free := ρ.free } =
        ExpRel (T⟪k + 1, T_arg⟫) { bound := R_arg :: ρ.bound, free := ρ.free } := by
      intro R_arg
      apply expRel_eq_of_valRel_eq
      have := valRel_bound_irr_at (ρ := ρ) (R := R_arg) (by simp) hLcArg
      let ρ' : SemEnv := { bound := R_arg :: ρ.bound, free := ρ.free }
      have h := ih (k := k + 1) (ρ := ρ') (by aesop) hLcT
      rw [←this]
      exact h
    simp [h_body]

/-- Opening a type syntactically is equivalent to evaluating that type into a `ValRel`
  and pushing it onto the bound environment semantically. -/
lemma expRel_openTy_bound_comm {T T_arg : Ty} {ρ : SemEnv} {t₁ t₂ : Tm}
    (hLcArg : T_arg.LcAt 0)
    (hLcT : T.LcAt 1) :
    ExpRel T { ρ with bound := ValRel T_arg ρ :: ρ.bound } t₁ t₂ ↔
    ExpRel (T⟪T_arg⟫) ρ t₁ t₂ := by
  have : ValRel T { ρ with bound := ValRel T_arg ρ :: ρ.bound } =
      ValRel (T⟪T_arg⟫) ρ := by
    rw [←List.insertIdx_cons]
    exact valRel_openTy_bound_at (by aesop) hLcT hLcArg
  rw [expRel_eq_of_valRel_eq this]


theorem fundamental {Γ t T} (hTyp : Γ ⊢ t ∶ T)
    {ρ δ₁ δ₂ γ₁ γ₂} (hValid : ρ.IsValid) (hEnv : EnvRel Γ ρ δ₁ δ₂ γ₁ γ₂) :
    ExpRel T ρ (t.psubst γ₁ δ₁) (t.psubst γ₂ δ₂) := by
  induction hTyp generalizing ρ δ₁ δ₂ γ₁ γ₂ with
  | var Γ x T _ _ _ =>
    simp only [Tm.psubst]
    have := hEnv.tm_rel (by assumption)
    exact expRel_of_valRel hValid this
  | lam L Γ T₁ T₂ t _ h ih =>
    simp only [Tm.psubst]
    apply expRel_lam
    · apply LcTm.lam (L ∪ t.fv)
      · apply psubst_lcTy
        · assumption
        · exact hEnv.δ₁_lc
      · intro x hX
        rw [psubst_openTm_comm (by aesop) hEnv.γ₁_lc]
        apply psubst_lcTm
        · have := h x (by aesop) |> typing_regularity_tm
          exact this
        · intro y
          by_cases hy : y = x
          · simp [hy, Function.update]
            constructor
          · simp only [Function.update, hy, ↓reduceDIte]
            exact hEnv.γ₁_lc y
        · intro Y
          exact hEnv.δ₁_lc Y
    · apply LcTm.lam (L ∪ t.fv)
      · apply psubst_lcTy
        · assumption
        · exact hEnv.δ₂_lc
      · intro x hX
        rw [psubst_openTm_comm (by aesop) hEnv.γ₂_lc]
        apply psubst_lcTm
        · have := h x (by aesop) |> typing_regularity_tm
          exact this
        · intro y
          by_cases hy : y = x
          · simp [hy, Function.update]
            constructor
          · simp only [Function.update, hy, ↓reduceDIte]
            exact hEnv.γ₂_lc y
        · intro Y
          exact hEnv.δ₂_lc Y
    · exact hValid
    · intro v₁ v₂ hVal
      have hLc_v₁ := valRel_candidate hValid |>.lc_left hVal
      have hLc_v₂ := valRel_candidate hValid |>.lc_right hVal
      have ⟨x, hx⟩ := exists_fresh_name (L ∪ t.fv)
      let γ₁' := Function.update γ₁ x v₁
      let γ₂' := Function.update γ₂ x v₂
      have hEnv' : EnvRel ((x, .tm T₁) :: Γ) ρ δ₁ δ₂ γ₁' γ₂' := by
        constructor
        · intro X hX
          have := hEnv.ty_rel (X := X) (by aesop)
          aesop
        · intro y T hy
          by_cases hyx : y = x
          · simp [hyx, γ₁', γ₂']
            subst hyx
            have hWf := h y (by aesop) |> typing_regularity_wf
            have := wf_lookup_mid (Γ₁ := []) (b₂ := .tm T) hWf (by aesop)
            aesop
          · simp only [ne_eq, hyx, not_false_eq_true, Function.update_of_ne, γ₁', γ₂']
            exact hEnv.tm_rel (by aesop)
        · exact hEnv.δ₁_lc
        · exact hEnv.δ₂_lc
        · intro y
          by_cases hyx : y = x
          · simp only [hyx, Function.update_self, γ₁']
            assumption
          · simp only [ne_eq, hyx, not_false_eq_true, Function.update_of_ne, γ₁']
            exact hEnv.γ₁_lc y
        · intro y
          by_cases hyx : y = x
          · simp only [hyx, Function.update_self, γ₂']
            assumption
          · simp only [ne_eq, hyx, not_false_eq_true, Function.update_of_ne, γ₂']
            exact hEnv.γ₂_lc y
      have := ih x (by aesop) hValid hEnv'
      rw [← psubst_openTm_comm', ← psubst_openTm_comm'] at this
      · assumption
      · aesop
      · exact hEnv.γ₂_lc
      · aesop
      · exact hEnv.γ₁_lc
  | app Γ t₁ t₂ T₁ T₂ _ _ ih₁ ih₂ =>
    simp only [Tm.psubst]
    apply expRel_app
    · apply ih₁ hValid hEnv
    · apply ih₂ hValid hEnv
  | tLam L Γ t T h ih =>
    simp only [Tm.psubst]
    have hLc_v₁ : LcTm (Λ' Tm.psubst γ₁ δ₁ t) := by
      apply LcTm.tLam (L ∪ t.fvTy)
      intro X hX
      rw [psubst_openTmTy_comm (by aesop) hEnv.γ₁_lc hEnv.δ₁_lc]
      apply psubst_lcTm
      · have := h X (by aesop) |> typing_regularity_tm
        exact this
      · exact hEnv.γ₁_lc
      · intro Y
        by_cases hY : Y = X
        · simp [hY, Function.update]
          constructor
        · simp only [Function.update, hY, ↓reduceDIte]
          exact hEnv.δ₁_lc Y
    have hLc_v₂ : LcTm (Λ' Tm.psubst γ₂ δ₂ t) := by
      apply LcTm.tLam (L ∪ t.fvTy)
      intro X hX
      rw [psubst_openTmTy_comm (by aesop) hEnv.γ₂_lc hEnv.δ₂_lc]
      apply psubst_lcTm
      · have := h X (by aesop) |> typing_regularity_tm
        exact this
      · exact hEnv.γ₂_lc
      · intro Y
        by_cases hY : Y = X
        · simp [hY, Function.update]
          constructor
        · simp only [Function.update, hY, ↓reduceDIte]
          exact hEnv.δ₂_lc Y
    apply expRel_tLam
    · assumption
    · assumption
    · intro R U₁ U₂ hR hLc_U₁ hLc_U₂
      have ⟨X, hX⟩ := exists_fresh_name (L ∪ t.fvTy ∪ T.fv ∪ Context.fv Γ)
      let δ₁' := Function.update δ₁ X U₁
      let δ₂' := Function.update δ₂ X U₂
      let ρ' := { ρ with bound := ρ.bound, free := Function.update ρ.free X R }
      have hEnv' : EnvRel ((X, .ty) :: Γ) ρ' δ₁' δ₂' γ₁ γ₂ := by
        constructor
        · intro Y hY
          by_cases hYX : Y = X
          · simp [ρ', δ₁', δ₂', hYX, Function.update]
            aesop
          · simp [δ₁', δ₂', hYX]
            have := hEnv.ty_rel (X := Y) (by aesop)
            simp [ρ', hYX]
            aesop
        · intro x T' hx
          have hx': (x, .tm T') ∈ Γ := by aesop
          have := hEnv.tm_rel hx'
          have : X ∉ T'.fv := by
            have : X ∉ Context.fv Γ := by aesop
            intro hIn
            have : T'.fv ⊆ Context.fv Γ := subset_fv_of_mem_tm hx'
            grind
          have := valRel_free_update_of_not_mem (R := R) (ρ := ρ) this
          simp only [this, ρ']
          assumption
        · intro Y
          by_cases hY : Y = X
          · simp only [hY, Function.update_self, δ₁']
            assumption
          · simp only [ne_eq, hY, not_false_eq_true, Function.update_of_ne, δ₁']
            exact hEnv.δ₁_lc Y
        · intro Y
          by_cases hY : Y = X
          · simp only [hY, Function.update_self, δ₂']
            assumption
          · simp only [ne_eq, hY, not_false_eq_true, Function.update_of_ne, δ₂']
            exact hEnv.δ₂_lc Y
        · exact hEnv.γ₁_lc
        · exact hEnv.γ₂_lc
      have hValid' : ρ'.IsValid := by
        simp [SemEnv.IsValid] at hValid
        simp only [SemEnv.IsValid]
        simp only [ρ']
        refine ⟨hValid.left, ?_⟩
        intro Y
        by_cases hY : Y = X
        · simp only [Function.update, hY, ↓reduceDIte, eq_rec_constant]
          exact hR
        · simp only [Function.update, hY, ↓reduceDIte]
          exact hValid.right Y
      have := ih X (by aesop) hValid' hEnv'
      apply expRel_step_back_right
      · constructor <;> assumption
      · apply SmallStep.tAppTLam <;> assumption
      apply expRel_step_back_left
      · constructor <;> assumption
      · apply SmallStep.tAppTLam <;> assumption
      have lcAt_t : T.LcAt 1 := by
        have := h X (by aesop) |> typing_regularity_ty
        have := lcAt_zero_of_lcTy this
        have := lcAtTy_of_openTy this
        simp [this]
      rw [←expRel_openTy_comm (by aesop) lcAt_t] at this
      rw [←psubst_openTmTy_comm' (by aesop) hEnv.γ₁_lc hEnv.δ₁_lc] at this
      rw [←psubst_openTmTy_comm' (by aesop) hEnv.γ₂_lc hEnv.δ₂_lc] at this
      assumption
  | tApp Γ t T₁ T₂ h _ ih =>
    have hExp_t := ih hValid hEnv
    have hLc_U₁ : LcTy (T₂.psubst δ₁) := by
      apply psubst_lcTy
      · assumption
      · exact hEnv.δ₁_lc
    have hLc_U₂ : LcTy (T₂.psubst δ₂) := by
      apply psubst_lcTy
      · assumption
      · exact hEnv.δ₂_lc
    have hApp := expRel_tApp (T_arg := T₂) hValid hLc_U₁ hLc_U₂ hExp_t
    rw [expRel_openTy_bound_comm] at hApp
    · exact hApp
    · exact lcAt_zero_of_lcTy (by assumption)
    · have := typing_regularity_ty h
      cases this with
      | all L T h =>
        have ⟨X, hX⟩ := exists_fresh_name L
        have := h X hX
        have := lcAt_zero_of_lcTy this
        have := lcAtTy_of_openTy this
        simp [this]

def SingletonRel (t : Tm) : TmRel :=
  fun t₁ t₂ => t₁ = t ∧ t₂ = t ∧ LcTm t ∧ Value t

theorem singletonRel_candidate (t : Tm) : IsValCandidateRel (SingletonRel t) := by
  constructor <;> simp [SingletonRel] <;> aesop

section

example : ∀ f, (∅ ⊢ f ∶ ∀' (#T0 ⇒ #T0)) →
    ∀ U u, LcTy U → LcTm u → Value u →
    f⦃U⦄ ◦ u ⟶* u := by
  intro f hTy U u hLcU hLcu hValu
  have hExp_f := fundamental hTy semEnv_empty_valid envRel_empty
  simp only [tm_psubst_id, ExpRel, exists_and_left, and_self_left] at hExp_f
  rcases hExp_f with ⟨_, v₁, hEval_v₁, _, _, hVal_f⟩
  simp only [ValRel] at hVal_f
  rcases hVal_f with ⟨_, _, _, _, ⟨body₁, rfl⟩, _, f_all⟩
  have h_inst := f_all (SingletonRel u) U U (singletonRel_candidate u) hLcU hLcU
  simp only [ExpRel, exists_and_left] at h_inst
  rcases h_inst with ⟨_, _, v_final₁, hEval_final₁, _, _, hVal_arr⟩
  simp only [ValRel, List.length_cons, lt_add_iff_pos_left, Order.lt_add_one_iff, zero_le,
    ↓reduceDIte, List.getElem_cons_zero] at hVal_arr
  rcases hVal_arr with ⟨_, _, _, _, ⟨A₁, ⟨body_final₁, rfl⟩⟩, _, f_arr⟩
  have h_u_rel : SingletonRel u u u := by
    simp only [SingletonRel, true_and]
    constructor <;> assumption
  have h_app := f_arr u u h_u_rel
  simp only [ExpRel, exists_and_left] at h_app
  rcases h_app with ⟨_, _, v_app_final₁, hEval_app_final₁, _, _, hVal_final⟩
  simp only [ValRel, List.length_cons, lt_add_iff_pos_left, Order.lt_add_one_iff, zero_le,
    ↓reduceDIte, List.getElem_cons_zero, SingletonRel] at hVal_final
  have : v_app_final₁ = u := by simp [hVal_final]
  subst this
  apply Relation.ReflTransGen.trans
  · apply multi_app₁
    · apply multi_tApp
      · exact hEval_v₁
      · assumption
    · assumption
  · apply Relation.ReflTransGen.trans
    · apply multi_app₁
      · exact hEval_final₁
      · assumption
    · assumption

example : ∀ f, (∅ ⊢ f ∶ ∀' #T0) → False := by
  intro f hTy
  have hExp_f := fundamental hTy semEnv_empty_valid envRel_empty
  simp only [tm_psubst_id, ExpRel, exists_and_left, and_self_left] at hExp_f
  rcases hExp_f with ⟨_, v₁, hEval_v₁, _, _, hVal_f⟩
  simp only [ValRel] at hVal_f
  rcases hVal_f with ⟨_, _, _, _, ⟨body₁, rfl⟩, _, f_all⟩
  -- A dummy closed type
  let T_dummy : Ty := $T"Dummy"
  have hLc_dummy: LcTy T_dummy := by constructor
  -- Instantiate with empty relation
  have h_inst := f_all (fun _ _ => False) T_dummy T_dummy (by simp) hLc_dummy hLc_dummy
  simp only [ExpRel, exists_and_left] at h_inst
  rcases h_inst with ⟨_, _, v_final₁, hEval_final₁, v_final₂, _, hVal_empty⟩
  -- Here `hVal_empty : 𝒱[#0]` says `v_final₁` and `v_final₂` are related, which is a contradiction!
  simp [ValRel] at hVal_empty

end

end SystemF.CBV

import SystemF.Subst.Ty

namespace SystemF


/-
  A type `T` is locally closed if its bound indices are properly bound.
  Here we use cofinite quantification.
  This is equivalent to `LcAtTy 0 T`.
-/
@[aesop safe constructors]
inductive LcTy : Ty → Prop where
  | fvar x : LcTy ($T x)
  | arr T₁ T₂ : LcTy T₁ → LcTy T₂ → LcTy (T₁ ⇒ T₂)
  | all (L : Finset Name) T : (∀ X ∉ L, LcTy (T⟪$T X⟫)) → LcTy (∀' T)

/-
  A simple locally closed type example.
-/
example : LcTy (∀' (#T 0 ⇒ #T 0)) := by
  apply LcTy.all ∅
  aesop

@[aesop safe forward]
theorem openTy_neq_id {k j : ℕ} {T U V : Ty} (hNeq : k ≠ j) (h : T⟪j, V⟫⟪k, U⟫ = T⟪j, V⟫) :
    T⟪k, U⟫ = T := by
  induction T generalizing k j with aesop

@[simp]
theorem openTy_lcTy_id {U : Ty} (h : LcTy U) (k : ℕ) (V : Ty) :
    U⟪k, V⟫ = U := by
  induction h generalizing k V with
  | fvar x => aesop
  | arr T₁ T₂ _ _ ih₁ ih₂ => aesop
  | all L T _ ih =>
    simp only [openTy_all, Ty.all.injEq]
    have ⟨X, hX⟩ := exists_fresh_name L
    have := @ih X hX (k + 1) V
    have := @openTy_neq_id (k + 1) 0 T V ($TX) (by aesop) (by assumption)
    rw [this]
/-
  Substitution commutes with opening on types
-/
@[aesop unsafe 70% apply]
theorem openTy_substTy_comm {k} {X Y : Name} {T U : Ty} (hNeq : X ≠ Y) (hU : LcTy U) :
    (T[X ↦ U])⟪k, ($T Y)⟫ = (T⟪k, $T Y⟫)[X ↦ U] := by
  induction T generalizing k with aesop

/-
  Substitution preserves locally closedness of types
-/
@[aesop safe apply]
theorem substTy_lcTy {T U : Ty} {X : Name} (hT : LcTy T) (hU : LcTy U) : LcTy (T[X ↦ U]) := by
  induction hT with
  | fvar x => aesop
  | arr T₁ T₂ _ _ ih₁ ih₂ => aesop
  | all L T _ ih =>
    simp only [subst_all]
    apply LcTy.all (L ∪ {X} ∪ U.fv)
    intro Y hY
    rw [openTy_substTy_comm] <;> aesop

@[aesop unsafe 70% apply]
theorem substTy_dist_openTy {T U V : Ty} {X : Name} {k : ℕ} (hU : LcTy U) :
    (T⟪k, V⟫)[X ↦ U] = (T[X ↦ U])⟪k, V[X ↦ U]⟫ := by
  induction T generalizing k with aesop
/-
  If `∀' T` is locally closed (meaning `T` is not closed) and `U` is locally closed,
  then opening `T` with `U` yields a locally closed type.
-/
@[aesop unsafe 50% apply]
theorem openTy_lcTy {T U : Ty} (hT : LcTy (∀' T)) (hU : LcTy U) : LcTy (T⟪U⟫) := by
  cases hT with
  | all L T h =>
    have ⟨X, hX⟩ := exists_fresh_name (L ∪ T.fv)
    specialize h X (by aesop)
    have := substTy_lcTy (X := X) h hU
    rw [←substTy_openTy_var (X := X) (by aesop)]
    apply this

end SystemF

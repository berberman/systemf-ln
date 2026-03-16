import Mathlib.Data.Finset.Basic
import Mathlib.Data.Set.Card

namespace SystemF


abbrev Name := String

@[aesop unsafe forward]
theorem exists_fresh_name (L : Finset Name) : ∃ x, x ∉ L := by
  apply L.exists_not_mem_of_card_lt_enatCard
  simp_all only [ENat.card_eq_top_of_infinite, ENat.coe_lt_top]

inductive Ty where
  | bvar (idx : ℕ)
  | fvar (name : Name)
  | arr (T₁ T₂ : Ty)
  | all (T : Ty)
deriving Repr, DecidableEq

inductive Tm where
  | bvar (idx : ℕ)
  | fvar (name : Name)
  | app (t₁ t₂ : Tm)
  | tApp (t : Tm) (T : Ty)
  | lam (T : Ty) (t : Tm)
  | tLam (t : Tm)
deriving Repr, DecidableEq

def Ty.size : Ty → ℕ
  | .bvar _ => 1
  | .fvar _ => 1
  | .arr T₁ T₂ => T₁.size + T₂.size + 1
  | .all T => T.size + 1

def Ty.fv : Ty → Finset Name
  | .fvar x => {x}
  | .bvar _ => ∅
  | .all T => fv T
  | .arr T₁ T₂ => T₁.fv ∪ T₂.fv

def Tm.fv : Tm → Finset Name
  | .fvar x => {x}
  | .tLam t => t.fv
  | .lam _ t => t.fv
  | .tApp t _ => t.fv
  | .app t₁ t₂ => t₁.fv ∪ t₂.fv
  | .bvar _ => ∅

def Tm.fvTy : Tm → Finset Name
  | .bvar _ => ∅
  | .fvar _ => ∅
  | .app t₁ t₂ => t₁.fvTy ∪ t₂.fvTy
  | .lam T t => T.fv ∪ t.fvTy
  | .tLam t => t.fvTy
  | .tApp t T => t.fvTy ∪ T.fv


scoped infixr:60 " ⇒ " => Ty.arr
scoped prefix:70 "∀' " => Ty.all
scoped prefix:90 "#T" => Ty.bvar
scoped prefix:90 "$T" => Ty.fvar
scoped notation:50 "ƛ " A " => " t => Tm.lam A t
scoped infixl:70 " ◦ " => Tm.app
scoped prefix:80 "Λ' " => Tm.tLam
scoped prefix:90 "#v" => Tm.bvar
scoped prefix:90 "$v" => Tm.fvar
scoped notation:70 t "⦃" A "⦄" => Tm.tApp t A

@[simp]
lemma ty_fv_fvar {x : Name} : Ty.fv ($T x) = {x} := rfl

@[simp]
lemma ty_fv_bvar {n : ℕ} : Ty.fv (#T n) = ∅ := rfl

@[simp]
lemma ty_fv_arr {T₁ T₂ : Ty} : Ty.fv (T₁ ⇒ T₂) = Ty.fv T₁ ∪ Ty.fv T₂ := rfl

@[simp]
lemma ty_fv_all {T : Ty} : Ty.fv (∀' T) = Ty.fv T := rfl

@[simp]
lemma tm_fv_fvar {x : Name} : Tm.fv ($v x) = {x} := rfl

@[simp]
lemma tm_fv_bvar {n : ℕ} : Tm.fv (#v n) = ∅ := rfl

@[simp]
lemma tm_fv_app {t₁ t₂ : Tm} : Tm.fv (t₁ ◦ t₂) = Tm.fv t₁ ∪ Tm.fv t₂ := rfl

@[simp]
lemma tm_fv_lam {T : Ty} {t : Tm} : Tm.fv (ƛ T => t) = Tm.fv t := rfl

@[simp]
lemma tm_fv_tLam {t : Tm} : Tm.fv (Λ' t) = Tm.fv t := rfl

@[simp]
lemma tm_fv_tApp {t : Tm} {T : Ty} : Tm.fv (t⦃T⦄) = Tm.fv t := rfl

@[simp]
lemma tm_fvTy_bvar {n : ℕ} : Tm.fvTy (#v n) = ∅ := rfl

@[simp]
lemma tm_fvTy_fvar {x : Name} : Tm.fvTy ($v x) = ∅ := rfl

@[simp]
lemma tm_fvTy_app {t₁ t₂ : Tm} : Tm.fvTy (t₁ ◦ t₂) = Tm.fvTy t₁ ∪ Tm.fvTy t₂ := rfl

@[simp]
lemma tm_fvTy_lam {T : Ty} {t : Tm} : Tm.fvTy (ƛ T => t) = T.fv ∪ Tm.fvTy t := rfl

@[simp]
lemma tm_fvTy_tLam {t : Tm} : Tm.fvTy (Λ' t) = Tm.fvTy t := rfl

@[simp]
lemma tm_fvTy_tApp {t : Tm} {T : Ty} : Tm.fvTy (t⦃T⦄) = Tm.fvTy t ∪ T.fv := rfl

@[simp]
lemma ty_size_bvar {n : ℕ} : Ty.size (#T n) = 1 := rfl

@[simp]
lemma ty_size_fvar {x : Name} : Ty.size ($T x) = 1 := rfl

@[simp]
lemma ty_size_arr {T₁ T₂ : Ty} : Ty.size (T₁ ⇒ T₂) = T₁.size + T₂.size + 1 := rfl

@[simp]
lemma ty_size_all {T : Ty} : Ty.size (∀' T) = T.size + 1 := rfl

end SystemF

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Set.Card

namespace SystemF


abbrev Name := String

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

end SystemF

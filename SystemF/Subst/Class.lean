import SystemF.Syntax

namespace SystemF
/-- Open `β` with `α` at index `k`, i.e. replacing bound variables at index `k` with `α` in `β`.
  `T⟪k, U⟫` opens `T` at index `k` with `U`.
  Here `T` is `β`, `k` is the index of the bound variable to be replaced, and `U` is `α`.
-/
class Open (α : Type) (β : Type) where
  «open» : ℕ → α → β → β

scoped notation T "⟪" k ", " U "⟫" => Open.open k U T
scoped notation T "⟪" U "⟫" => Open.open 0 U T


/-- Substitute free variable with `α` in `β`.
  `T[X ↦ U]` substitutes free type variable `X` with `U` in `T`.
  Here `T` is `β`, `X` is `Name`, and `U` is `α`.
-/
class Subst (α : Type) (β : Type) where
  subst : Name → α → β → β

scoped syntax:max term:max noWs "[" term " ↦ " term "]" : term
macro_rules
  | `($A[$X ↦ $U]) => ``(Subst.subst $X $U $A)
@[scoped app_unexpander Subst.subst]
meta def unexpandSubst : Lean.PrettyPrinter.Unexpander
  | `($_ $X $U $A) => ``($A[$X ↦ $U])
  | _              => throw ()

end SystemF

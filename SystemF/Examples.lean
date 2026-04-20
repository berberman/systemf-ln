import SystemF.Syntax
import SystemF.Typing

namespace SystemF.Examples

def Bool := ∀' (#T0 ⇒ #T0 ⇒ #T0)

def true := Λ' (ƛ #T0 => ƛ #T0 => #v1)
def false := Λ' (ƛ #T0 => ƛ #T0 => #v0)

example : ∅ ⊢ true ∶ Bool := by
  apply HasType.tLam ∅
  intro X hX
  apply HasType.lam {X}
  · constructor
  · intro x hx
    apply HasType.lam {X, x}
    · constructor
    · intro y hy
      constructor
      · constructor
        · constructor
          · constructor
            · constructor
            · aesop
          · aesop
          · constructor
        · aesop
        · constructor
      · aesop
      · constructor

end SystemF.Examples

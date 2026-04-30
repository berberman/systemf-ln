import SystemF.Syntax.Named
import SystemF.Typing

namespace SystemF.Examples

open SystemF.NamedNotation

def Bool := [ty| ∀ X. X → X → X]

def true := [tm| Λ X. λ t : X. λ f : X. t]
def false := [tm| Λ X. λ t : X. λ f : X. f]

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

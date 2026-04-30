# System F in Lean 4

Formalization of System F using the **Locally Nameless** representation in Lean 4 for practice.

## Project Structure

- `SystemF/Syntax.lean`, `SystemF/Syntax/`: the core Abstract Syntax Tree (`Tm` for terms and `Ty` for types).
- `SystemF/Lc.lean`, `SystemF/Lc/`: local closure predicates (`LcTm` and `LcTy`).
- `SystemF/Subst.lean`, `SystemF/Subst/`: substitution operations and the lemmas.
- `SystemF/Context.lean`: typing environments for locally nameless abstractions.
- `SystemF/Typing.lean`: typing relation `Γ ⊢ t ∶ T`.
- `SystemF/CBV/Semantics.lean`: operational semantics, `Value` predicates, and small-step CBV reduction (`t ⟶ t'`).
- `SystemF/CBV/Safety.lean`: canonical forms lemmas, Type Preservation, and the Progress theorem.
- `SystemF/CBV/Parametricity.lean`: relational interpretation of types and contexts, concluding with the Fundamental Theorem of Logical Relations.

## References

- Arthur Charguéraud, [*The Locally Nameless Representation*](https://chargueraud.org/research/2009/ln/main.pdf)
- PLClub, [*metalib*](https://github.com/plclub/metalib)
- Jean-Yves Girard, Paul Taylor, and Yves Lafont, [*Proofs and Types*](https://www.paultaylor.eu/stable/prot.pdf)
- Lau Skorstengaard, [*An Introduction to Logical Relations*](https://www.cs.uoregon.edu/research/summerschool/summer16/notes/AhmedLR.pdf)

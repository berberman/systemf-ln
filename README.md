# System F in Lean 4

Formalization of Church-style System F using the **Locally Nameless** representation in Lean 4 for practice.

## Project Structure

- `SystemF/Syntax.lean`, `SystemF/Syntax/`: the core Abstract Syntax Tree (`Tm` for terms and `Ty` for types).
- `SystemF/Lc.lean`, `SystemF/Lc/`: local closure predicates (`LcTm` and `LcTy`).
- `SystemF/Subst.lean`, `SystemF/Subst/`: substitution operations and the lemmas.
- `SystemF/Context.lean`: typing environments for locally nameless abstractions.
- `SystemF/Typing.lean`: typing relation `Γ ⊢ t ∶ T`.
- `SystemF/CBV/Semantics.lean`: operational semantics, `Value` predicates, and small-step CBV reduction (`t ⟶ t'`).
- `SystemF/CBV/Safety.lean`: canonical forms lemmas, Type Preservation, and the Progress theorem.
- `SystemF/CBV/Parametricity.lean`: binary relational interpretation of types and contexts, concluding with the parametricity examples.
- `SystemF/SN.lean`: well-typed terms are strongly normalizing.

## References

- Arthur Charguéraud, [*The Locally Nameless Representation*](https://chargueraud.org/research/2009/ln/main.pdf)
- Brian Aydemir, Benjamin C. Pierce, Randy Pollock, and Stephanie Weirich, [*Engineering Formal Metatheory*](https://www.cis.upenn.edu/~bcpierce/papers/binders.pdf) 
- Jean-Yves Girard, Paul Taylor, and Yves Lafont, [*Proofs and Types*](https://www.paultaylor.eu/stable/prot.pdf)
- Jean H. Gallier, [*On Girard's Candidats De Réductibilité*](https://www.cis.upenn.edu/~jean/sngirard.pdf)
- Lau Skorstengaard, [*An Introduction to Logical Relations*](https://www.cs.uoregon.edu/research/summerschool/summer16/notes/AhmedLR.pdf)
- Thorsten Altenkirch, [*A Formalization of the Strong Normalization Proof for System F in LEGO*](https://people.cs.nott.ac.uk/psztxa/publ/tlca93.pdf)
- Kevin Donnelly and Hongwei Xi, [*A Formalization of Strong Normalization for Simply-Typed Lambda-Calculus and System F*](https://dl.acm.org/doi/abs/10.1016/j.entcs.2007.01.021)
- PLClub, [*metalib*](https://github.com/plclub/metalib)
- Yiyun Liu, [*Strong normalization and parametricity for System F Omega in Coq*](https://github.com/yiyunliu/system-f-omega)

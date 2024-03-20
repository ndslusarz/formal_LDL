# Logic of Differentiable Logics in Coq

This repository contains the formalization of the Logic of
Differentiable Logics (LDL) using the Coq proof-assistant and the
Mathematical Components library.

The LDL language is defined in `ldl.v`, along with its fuzzy, DL2, STL
and Boolean interpretations.  The files `fuzzy.v`, `dl2.v`,
`dl2_ereal.v`, `stl.v` and `stl_ereal.v` contain the relevant theorems
that hold for each interpretation: structural properties (idempotence,
commutativity and associativity of operators), soundness, and
shadow-lifting.

## Meta
- Authors:
  - Natalia Ślusarz
  - Reynald Affeldt
  - Alessandro Bruni
- Compatible Coq versions: Coq 8.18 to 8.19
- Additional dependencies:
  - [MathComp analysis 1.0.0](https://github.com/math-comp/analysis) and its dependencies

## Setup instructions

Create an opam switch with the Coq repository:
```sh
opam switch create ldl 4.14.1
eval $(opam env --switch=ldl)
opam repo add coq-released https://coq.inria.fr/opam/released
```

Install the dependencies:

```sh
opam install coq-mathcomp-analysis.1.0.0 coq-mathcomp-algebra-tactics.1.2.3
```

Compile this project:

```sh
make
```

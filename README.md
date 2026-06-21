<!---
This file was generated from `meta.yml`, please do not edit manually.
Follow the instructions on https://github.com/coq-community/templates to regenerate.
--->
# Formalisation of Differentiable Logics

[![Docker CI][docker-action-shield]][docker-action-link]

[docker-action-shield]: https://github.com/formal-LDL/formal-LDL/actions/workflows/docker-action.yml/badge.svg?branch=master
[docker-action-link]: https://github.com/formal-LDL/formal-LDL/actions/workflows/docker-action.yml




This repository contains the formalization of the Logic of
Differentiable Logics (LDL) using the Rocq prover and the
Mathematical Components library.
The LDL language is defined in `ldl.v`, along with its fuzzy, DL2, STL, STLinfty
and Boolean interpretations.  The files `fuzzy.v`, `dl2.v`,
`dl2_ereal.v`, `stl.v`, `stl_ereal.v` and `stl_infty.v` contain the relevant theorems
that hold for each interpretation: structural properties based on
residuated lattices (idempotence,
commutativity and associativity of operators, residuation, prelinearity etc.),
 adequacy, and shadow-lifting.

The formalisation of soundness of hypersequent calculi for fuzzy logics can
be found in file `seq_calc.v`, for DL2 in `dl2_seq_calc.v` and for STLinfty
in `stl_infty_seq_calc.v`.

## Meta

- Author(s):
  - Reynald Affeldt (initial)
  - Alessandro Bruni (initial)
  - Natalia Ślusarz (initial)
  - Kathrin Stark (initial)
  - Ekaterina Komendantskaya (initial)
- License: [MIT License](LICENSE)
- Additional dependencies:
  - [MathComp](https://math-comp.github.io)
  - [MathComp Analysis](https://github.com/math-comp/analysis)
  - [MathComp Algebra Tactics](https://github.com/math-comp/algebra-tactics)
- Related publication(s):
  - [Taming Differentiable Logics with Coq Formalisation (arXiv)](https://arxiv.org/abs/2403.13700) 
  - [Taming Differentiable Logics with Coq Formalisation (LIPIcs)](https://doi.org/10.4230/LIPIcs.ITP.2024.4) 

## Building and installation instructions

The easiest way to install the latest released version of Formalisation of Differentiable Logics
is via [OPAM](https://opam.ocaml.org/doc/Install.html):

```shell
opam repo add rocq-released https://rocq-prover.org/opam/released
opam install coq-formal-LDL
```

To instead build and install manually, you need to make sure that all the
libraries this development depends on are installed.  The easiest way to do that
is still to rely on opam:

``` shell
git clone https://github.com/formal-LDL/formal-LDL.git
cd formal-LDL
opam repo add rocq-released https://rocq-prover.org/opam/released
opam install --deps-only .
make   # or make -j <number-of-cores-on-your-machine> 
make install
```




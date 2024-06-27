<!---
This file was generated from `meta.yml`, please do not edit manually.
Follow the instructions on https://github.com/coq-community/templates to regenerate.
--->
# Formalisation of Differentiable Logics

[![Docker CI][docker-action-shield]][docker-action-link]

[docker-action-shield]: https://github.com/formal-LDL/formal-LDL/actions/workflows/docker-action.yml/badge.svg?branch=master
[docker-action-link]: https://github.com/formal-LDL/formal-LDL/actions/workflows/docker-action.yml




This repository contains the formalization of the Logic of
Differentiable Logics (LDL) using the Coq proof-assistant and the
Mathematical Components library.
The LDL language is defined in `ldl.v`, along with its fuzzy, DL2, STL
and Boolean interpretations.  The files `fuzzy.v`, `dl2.v`,
`dl2_ereal.v`, `stl.v` and `stl_ereal.v` contain the relevant theorems
that hold for each interpretation: structural properties (idempotence,
commutativity and associativity of operators), soundness, and shadow-lifting.

## Meta

- Author(s):
  - Reynald Affeldt (initial)
  - Alessandro Bruni (initial)
  - Natalia Slusarz (initial)
  - Katrhin Stark (initial)
  - Ekaterina Komendantskaya (initial)
- License: [MIT License](LICENSE)
- Compatible Coq versions: 8.18 to 8.19
- Additional dependencies:
  - [MathComp](https://math-comp.github.io) 2.0
  - [MathComp Analysis](https://github.com/math-comp/analysis) 1.0.0
  - [MathComp Algebra Tactics](https://github.com/math-comp/algebra-tactics) 1.2.3
- Related publication(s):
  - [Taming Differentiable Logics with Coq Formalisation](https://arxiv.org/abs/2403.13700) 

## Building and installation instructions

The easiest way to install the latest released version of Formalisation of Differentiable Logics
is via [OPAM](https://opam.ocaml.org/doc/Install.html):

```shell
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq-formal-LDL
```

To instead build and install manually, do:

``` shell
git clone https://github.com/formal-LDL/formal-LDL.git
cd formal-LDL
make   # or make -j <number-of-cores-on-your-machine> 
make install
```




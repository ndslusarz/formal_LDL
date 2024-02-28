# LDL_coq

Repo for formalisation attempt of LDL in Coq. 

Parts of formalisation left, sorted by DL:
- STL
  + share stl_and_gt0 and stl_and_lt0 with the ldl.v (so that the shadow-lifting proof used the exact same function) - will need to refactor some proofs for this
  + shadow lifting (split into two parts - lt0, gt0)
  + paper sketch of proof for the half missing from STL paper


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

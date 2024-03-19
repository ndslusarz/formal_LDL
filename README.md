# LDL_coq

Repo for formalisation of LDL in Coq. 
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

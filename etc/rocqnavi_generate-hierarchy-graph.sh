#!/bin/sh
## Emit the Hierarchy-Builder structure graph that `rocqnavi -structure-graph`
## renders on the index page.  Requiring dl_structures.v is what makes the DL
## hierarchy (tnormType ... mvType) show up, together with the mathcomp Order
## and algebra structures it sits on top of.
##
## NB: this goes through `rocq compile` rather than piping into `coqtop` on
## purpose.  coqtop exits 0 even when `Require` fails -- which happens as soon
## as dl_structures.vo was built by a different OCaml toolchain than the coqtop
## on PATH -- and HB.graph then writes an empty `digraph Hierarchy { }`, leaving
## a blank graph on the index page and no indication that anything went wrong.
set -e

DST=$1
MODULE=${2:-LDL.dl_structures}
if [ -z "$DST" ]; then
  echo "usage: $0 <output.dot> [module]" >&2
  exit 2
fi

## Compiled in the project root so that HB.graph's relative output path and the
## -R load path both resolve; named so it cannot collide with a source file.
STEM=hierarchy_graph_tmp
trap 'rm -f $STEM.v $STEM.vo $STEM.vos $STEM.vok $STEM.glob .$STEM.aux' EXIT

cat > $STEM.v <<ROCQEOF
From HB Require Import structures.
Require Import $MODULE.
HB.graph "$DST".
ROCQEOF

${ROCQ:-rocq} compile -R . LDL $STEM.v > /dev/null

## Belt and braces: HB.graph can succeed and still produce nothing useful.
if ! grep -q -- '->' "$DST"; then
  echo "$0: $DST has no edges -- the hierarchy would render blank." >&2
  echo "Is $MODULE up to date and built by the Rocq on PATH?" >&2
  exit 1
fi

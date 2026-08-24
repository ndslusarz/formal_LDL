#!/bin/sh
## Build the file dependency graph that `rocqnavi -file-graph` renders on the
## index page, from `coqdep` output.
##
## NB: rocqnavi has a `-file-graph-from-depend` option that reads coqdep output
## directly, but its URL derivation is unusable for a flat project like this
## one.  In file_graph.ml, `parse_filepath` only consults the `-Q` directory
## mappings when the path contains a '/':
##
##     | [base] -> ([], Filename.remove_extension base, ext)
##
## so a bare "fuzzy.vo" never picks up the LDL namespace and every node links
## to ".fuzzy.html" instead of "LDL.fuzzy.html".  Projects that keep their
## sources in subdirectories (mathcomp-analysis has theories/, classical/, ...)
## do not hit this, which is why they can get away with generating the graph
## themselves and passing `-file-graph`, as we do here.
set -e

DST=$1
NAMESPACE=${2:-LDL}
if [ -z "$DST" ]; then
  echo "usage: $0 <output.dot> [namespace]" >&2
  exit 2
fi

coqdep -f _CoqProject | awk -v ns="$NAMESPACE" '
  ## Keep only local, top-level modules: external dependencies come through
  ## with absolute paths and would not have a page to link to.
  function local_module(m) { return m !~ /\// && m != "" }

  /\.vo.*:/ {
    split($0, sides, ":")
    split(sides[1], lhs, " ")
    tgt = lhs[1]
    sub(/\.vo$/, "", tgt)
    if (!local_module(tgt)) next
    nodes[tgt] = 1

    n = split(sides[2], rhs, " ")
    for (i = 1; i <= n; i++) {
      dep = rhs[i]
      if (dep ~ /\.vo$/) {
        sub(/\.vo$/, "", dep)
        if (local_module(dep)) candidates[dep "\t" tgt] = 1
      }
    }
  }

  END {
    ## The graph name matters: graphviz names the imagemap after it, and
    ## rocqnavi emits a hardcoded usemap="#depend" on the index page.  Any
    ## other name leaves the image with nothing to bind to, i.e. a graph that
    ## renders but is not clickable.
    print "digraph depend {"
    print "  node [shape=ellipse, style=filled, fillcolor=\"#dbc3b6\"];"
    for (m in nodes)
      printf "  \"%s\" [label=\"%s\", URL=\"%s.%s.html\"];\n", m, m, ns, m
    for (e in candidates) {
      split(e, pair, "\t")
      if (pair[1] in nodes && pair[2] in nodes)
        printf "  \"%s\" -> \"%s\";\n", pair[1], pair[2]
    }
    print "}"
  }
' > "$DST"

if ! grep -q -- '->' "$DST"; then
  echo "$0: $DST has no edges -- the dependency graph would render blank." >&2
  exit 1
fi

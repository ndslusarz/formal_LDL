all: Makefile.coq
	$(MAKE) -f Makefile.coq all

clean: Makefile.coq
	$(MAKE) -f Makefile.coq cleanall
	rm -f Makefile.coq Makefile.coq.conf

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq

_CoqProject Makefile: ;

%: Makefile.coq
	$(MAKE) -f Makefile.coq $@

.PHONY: all clean doc doc-clean

# Html documentation ---------------------------------------------------------
# `make doc` renders the sources with rocqnavi
# (https://github.com/affeldt-aist/rocqnavi), which `nix-shell` provides; see
# .nix/rocq-overlays/rocqnavi.  Outside nix, install it with
# `opam pin rocq-navi https://github.com/affeldt-aist/rocqnavi.git`.

DOCDIR = html
GIT_HASH := $(shell git describe --tags --exact-match 2>/dev/null || \
                    git rev-parse --short HEAD)
ROCQ_STDLIB_URL = https://rocq-prover.org/doc/V9.1.0/stdlib/
MATHCOMP_URL = https://math-comp.github.io/htmldoc_2_5_0/
ANALYSIS_URL = https://math-comp.github.io/analysis/htmldoc/1_16_0/

# File dependency graph, drawn on the index page.
$(DOCDIR)/dependency_graph.d: _CoqProject
	mkdir -p $(DOCDIR)
	coqdep -f _CoqProject > $@

# Hierarchy-Builder structure graph, likewise.  Needs the .vo files, hence
# the dependency on `all`.
$(DOCDIR)/hierarchy_graph.dot: all etc/rocqnavi_generate-hierarchy-graph.sh
	mkdir -p $(DOCDIR)
	etc/rocqnavi_generate-hierarchy-graph.sh $@

doc: all $(DOCDIR)/dependency_graph.d $(DOCDIR)/hierarchy_graph.dot
	rocqnavi \
	  -title "LDL $(GIT_HASH)" \
	  -d $(DOCDIR) \
	  -Q . LDL \
	  -coqlib $(ROCQ_STDLIB_URL) \
	  -file-graph-from-depend $(DOCDIR)/dependency_graph.d \
	  -structure-graph $(DOCDIR)/hierarchy_graph.dot \
	  -index-blacklist etc/rocqnavi_index-blacklist \
	  -external $(MATHCOMP_URL) mathcomp.ssreflect \
	  -external $(MATHCOMP_URL) mathcomp.algebra \
	  -external $(MATHCOMP_URL) mathcomp.order \
	  -external $(ANALYSIS_URL) mathcomp.analysis \
	  -external $(ANALYSIS_URL) mathcomp.classical \
	  -external $(ANALYSIS_URL) mathcomp.reals \
	  ./*.v ./*.glob

doc-clean:
	rm -rf $(DOCDIR)

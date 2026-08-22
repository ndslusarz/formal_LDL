## coq-nix-toolbox puts `rocqPackages.vscoq-language-server` on the nix-shell
## PATH whenever that attribute exists (see `vscoq` in the toolbox's
## default.nix).  nixpkgs' `rocqPackages` only carries the renamed
## `vsrocq-language-server` though -- the old name survives in `coqPackages`
## only -- so the toolbox never finds it.  Aliasing it under the name the
## toolbox looks for is what makes `vsrocqtop` available in `nix-shell`.
##
## Drop this overlay once the toolbox knows about `vsrocq-language-server`.
{ vsrocq-language-server }:
vsrocq-language-server

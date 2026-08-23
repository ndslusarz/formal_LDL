## rocqnavi is the HTML documentation generator used by `make doc`.  It is an
## OCaml tool rather than a Rocq library, and it is not in nixpkgs, so we build
## it from its latest release here.  The formal-LDL overlay pulls it in through
## `nativeBuildInputs`, which is what puts it on the `nix-shell` PATH.
##
## The opam package is called `rocq-navi`; the executable it installs is
## `rocqnavi`.  Note that upstream also carries `v1.x` tags inherited from
## coq2html, which are *older* than the `rocqnavi.X.Y.Z` ones -- 0.5.1 is the
## current release.  To update, bump `version` and replace `hash` with what
## `nix-prefetch-url --unpack` reports (converted with
## `nix hash convert --to sri`).
{ lib, stdenv, fetchFromGitHub, ocamlPackages }:

stdenv.mkDerivation rec {
  pname = "rocqnavi";
  version = "0.5.1";

  src = fetchFromGitHub {
    owner = "affeldt-aist";
    repo = "rocqnavi";
    rev = "rocqnavi.${version}";
    hash = "sha256-QfEP4qBbP0FLoxnjLe26tmZCpMg7Xu/gk6OXxL6Fdc4=";
  };

  nativeBuildInputs = with ocamlPackages; [ ocaml findlib ];
  buildInputs = with ocamlPackages; [ dune-glob yojson ];

  ## The default `all` target also builds the bundled ocamldot, which the
  ## `install` target does not install and which rocqnavi does not need: it
  ## shells out to graphviz at run time.
  buildFlags = [ "rocqnavi" ];

  installFlags = [ "PREFIX=$(out)" ];

  meta = with lib; {
    description = "HTML documentation generator for Rocq, an extension of coq2html";
    homepage = "https://github.com/affeldt-aist/rocqnavi";
    license = licenses.gpl2Plus;
    mainProgram = "rocqnavi";
    platforms = platforms.all;
  };
}

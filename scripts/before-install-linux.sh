#!/usr/bin/env bash
set -euv

(
mkdir -p opam
OPAMINSTALLER="https://raw.github.com/ocaml/opam/master/shell/opam_installer.sh"
wget $OPAMINSTALLER -O - | sh -s $TRAVIS_BUILD_DIR/opam
) || exit 1

export PATH=$TRAVIS_BUILD_DIR/opam:$PATH
opam init --no-setup
opam switch 4.02.3
eval `opam config env`
opam install --yes camlp5 ocamlfind ppx_import cmdliner core_kernel sexplib ppx_sexp_conv

sh ./scripts/before-install-coq.sh
sh ./scripts/before-install-coq-serapi.sh

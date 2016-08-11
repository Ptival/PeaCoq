#!/usr/bin/env bash
set -euv

PKGMGR="brew"

$PKGMGR update

# Haskell server
$PKGMGR install cabal-install ghc
cabal update
cabal install alex happy

# Coq and OCaml plugin
$PKGMGR install ocaml camlp5 opam
opam init --no-setup
opam switch 4.02.3
eval `opam config env`
opam install --yes camlp5 ocamlfind ppx_import cmdliner core_kernel sexplib ppx_sexp_conv

sh ./scripts/before-install-coq.sh
sh ./scripts/before-install-coq-serapi.sh

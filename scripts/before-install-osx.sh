#!/usr/bin/env bash
set -euv

COQVER="8.5pl1"
COQ="coq-8.5pl1"
PKGMGR="brew"

$PKGMGR update

# Haskell server
$PKGMGR install cabal-install ghc
cabal update
cabal install alex happy

# Coq and OCaml plugin
$PKGMGR install ocaml camlp5
# Brew packages a version of coq that was not built with its version of
# ocaml so coq complains
if [ ! -d "$HOME/$COQ" ]; then
  wget https://coq.inria.fr/distrib/V$COQVER/files/$COQ.tar.gz
  tar -xzvf $COQ.tar.gz
  ( cd $COQ
    ./configure -local
    make -j2
    make install
  ) || exit 1
else
  echo "Using coq from cache"
fi

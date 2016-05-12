#!/usr/bin/env bash
set -euv

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
if [ ! -d "$TRAVIS_BUILD_DIR/coq-$COQVER" ]; then
  wget https://coq.inria.fr/distrib/V$COQVER/files/coq-$COQVER.tar.gz
  tar -xzvf coq-$COQVER.tar.gz
  ( cd coq-$COQVER
    ./configure -local
    make -j2
    make install
  ) || exit 1
else
  echo "Using coq from cache"
fi

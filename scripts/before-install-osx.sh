#!/usr/bin/env bash
set -euv

PKGMGR="brew"

$PKGMGR update

# Haskell server
$PKGMGR install cabal-install ghc
#export PATH=/opt/ghc/$GHCVER/bin:/opt/cabal/$CABALVER/bin:$PATH
cabal update
cabal install alex happy
#export PATH=/opt/alex/$ALEXVER/bin:/opt/happy/$HAPPYVER/bin:$PATH

# Coq and OCaml plugin
$PKGMGR install coq ocaml camlp5
# Brew packages a version of coq that was not built with its version of
# ocaml so coq complains
wget https://coq.inria.fr/distrib/V8.5pl1/files/coq-8.5pl1.tar.gz
tar -xzvf coq-8.5pl1.tar.gz
( cd coq-8.5pl1
  yes "" | ./configure
  make
  sudo make install
) || exit 1

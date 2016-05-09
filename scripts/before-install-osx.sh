#!/bin/bash
set -ev

ALEXVER=3.1.4
HAPPYVER=1.19.5
PKGMGR="brew"

$PKGMGR update

# Haskell server
$PKGMGR install cabal-install ghc
export PATH=/opt/ghc/$GHCVER/bin:/opt/cabal/$CABALVER/bin:$PATH
cabal update
cabal install alex-$ALEXVER happy-$HAPPYVER
export PATH=/opt/alex/$ALEXVER/bin:/opt/happy/$HAPPYVER/bin:$PATH

# Coq and OCaml plugin
$PKGMGR install coq ocaml camlp5

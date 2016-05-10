#!/bin/bash
set -euv

COQVER=8.5
OCAMLVER=4.02.3
PKGMGR="sudo apt-get"

$PKGMGR update

# Haskell server
sudo add-apt-repository -y ppa:hvr/ghc
$PKGMGR update
$PKGMGR install cabal-install-$CABALVER ghc-$GHCVER
export PATH=/opt/cabal/$CABALVER/bin:$PATH
cabal update
$PKGMGR install alex-$ALEXVER happy-$HAPPYVER

# Coq and OCaml plugin
$PKGMGR install coq-$COQVER ocaml-$OCAMLVER camlp5

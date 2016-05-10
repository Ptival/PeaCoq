#!/bin/bash
set -euv

# ALEXVER=3.1.4
# CABALVER=1.22
# GHCVER=7.10.2
# HAPPYVER=1.19.5
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
$PKGMGR install coq ocaml camlp5

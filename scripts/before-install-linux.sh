#!/bin/bash
set -euv

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
$PKGMGR install ocaml camlp5
# Trusty packages 8.4, so we need to install manually?
wget https://coq.inria.fr/distrib/V8.5pl1/files/coq-8.5pl1.tar.gz
tar -xzvf coq-8.5pl1.tar.gz
( cd coq-8.5pl1
  ./configure
  sudo make
  sudo make install
)

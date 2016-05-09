#!/bin/bash
set -ev

PKGMGR="travis_retry sudo apt-get"

sudo add-apt-repository -y ppa:hvr/ghc
$PKGMGR update
$PKGMGR install cabal-install-$CABALVER
$PKGMGR install ghc-$GHCVER
export PATH=/opt/ghc/$GHCVER/bin:/opt/cabal/$CABALVER/bin:$PATH
$PKGMGR install alex-$ALEXVER
$PKGMGR install happy-$HAPPYVER
export PATH=/opt/alex/$ALEXVER/bin:/opt/happy/$HAPPYVER/bin:$PATH


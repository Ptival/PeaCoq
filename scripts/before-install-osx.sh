#!/bin/bash
set -ev

PKGMGR="brew"

$PKGMGR update
$PKGMGR install cabal-install
$PKGMGR install ghc-$GHCVER
export PATH=/opt/ghc/$GHCVER/bin:/opt/cabal/$CABALVER/bin:$PATH
cabal update
cabal install alex-$ALEXVER
cabal install happy-$HAPPYVER
export PATH=/opt/alex/$ALEXVER/bin:/opt/happy/$HAPPYVER/bin:$PATH

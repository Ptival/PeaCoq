#!/bin/bash
set -ev

ALEXVER="3.1.4"
CABALVER="1.22.9.0"
GHCVER="7.10.3b"
HAPPYVER="1.19.5"
PKGMGR="brew"

$PKGMGR update
$PKGMGR install cabal-install-$CABALVER
$PKGMGR install ghc-$GHCVER
export PATH=/opt/ghc/$GHCVER/bin:/opt/cabal/$CABALVER/bin:$PATH
cabal update
cabal install alex-$ALEXVER
cabal install happy-$HAPPYVER
export PATH=/opt/alex/$ALEXVER/bin:/opt/happy/$HAPPYVER/bin:$PATH

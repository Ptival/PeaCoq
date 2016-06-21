#!/usr/bin/env bash
set -euv

CABALFLAGS=""

cd peacoqtop

cabal install --only-dependencies --enable-tests ${CABALFLAGS}
cabal configure --enable-tests ${CABALFLAGS}
cabal build -j2
cabal copy
cabal register

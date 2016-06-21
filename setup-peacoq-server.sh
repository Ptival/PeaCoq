#!/usr/bin/env bash
set -euv

if [ -n "${NIX_LDFLAGS+x}" ] && [ -n "${NIX_CFLAGS_COMPILE+x}" ]; then
  INCLUDEDIR=`echo ${NIX_CFLAGS_COMPILE} | grep -o '/nix/store\S*zlib\S*/include' | head -1`
  echo "Setting --extra-include-dirs to: ${INCLUDEDIR}"
  LIBDIR=`echo ${NIX_LDFLAGS} | grep -o '/nix/store\S*zlib\S*[0-9]/lib' | head -1`
  echo "Setting --extra-lib-dirs to: ${LIBDIR}"
  CABALFLAGS="--extra-include-dirs=${INCLUDEDIR} --extra-lib-dirs=${LIBDIR}"
else
  LIBDIR=""
  CABALFLAGS=""
fi

cd peacoq-server

cabal install --only-dependencies --enable-tests ${CABALFLAGS}
cabal configure --enable-tests ${CABALFLAGS}
cabal build -j2
cabal copy
cabal register

# this path is ridiculous!
ln -sf peacoq-server/dist/build/peacoq-server/peacoq-server ../peacoq

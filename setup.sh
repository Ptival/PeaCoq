#!/usr/bin/env bash
set -euv

function missing {
  echo >&2 "$1 is missing. Please install it."
  echo >&2 "If you are running NixOS, run nix-shell."
  exit 1
}

function log {
  echo -e "\n\nPEACOQ: $1\n\n"
}

cabal --version >/dev/null 2>&1 || missing "cabal-install"
camlp5 -v       >/dev/null 2>&1 || missing "camlp5"
coqc -v         >/dev/null 2>&1 || missing "coq"
ocamlc -v       >/dev/null 2>&1 || missing "ocaml"

if [ -v "NIX_LDFLAGS" ] && [ -v "NIX_CFLAGS_COMPILE" ]; then
  INCLUDEDIR=`echo ${NIX_CFLAGS_COMPILE} | grep -o '/nix/store\S*zlib\S*/include' | head -1`
  echo "Setting --extra-include-dirs to: ${INCLUDEDIR}"
  LIBDIR=`echo ${NIX_LDFLAGS} | grep -o '/nix/store\S*zlib\S*[0-9]/lib' | head -1`
  echo "Setting --extra-lib-dirs to: ${LIBDIR}"
  CABALFLAGS="--extra-include-dirs=${INCLUDEDIR} --extra-lib-dirs=${LIBDIR}"
else
  LIBDIR=""
  CABALFLAGS=""
fi

log "Fetching Haskell dependencies"
cabal install --only-dependencies ${CABALFLAGS}
log "Configuring Haskell package"
cabal configure --enable-tests
log "Building Haskell package"
cabal build

log "Building OCaml plugin"
( cd plugin
  make -B
)

( cd web
  log "Installing npm dependencies"
  npm install
  cd js/peacoq-ts/
  log "Installing typings"
  ../../node_modules/typings/dist/bin.js install
  log "Transpiling front-end"
  ../../node_modules/typescript/bin/tsc -p .
)

# TODO: the config file should not go in HOME, it's annoying for everyone
# TODO: this config should be shared with the Haskell code somehow

log "Setting up configuration file"
PEACOQPATH=`pwd`
CONFIGPATH="${HOME}"
PEACOQCONFIG=".PeaCoqConfig.hs"
FILE="${CONFIGPATH}/${PEACOQCONFIG}"
LOGPATH="/tmp"

cat <<END > ${FILE}
PeaCoqConfig
{ configUserId = ""
, configLogPath = "${LOGPATH}"
, configCoqtop = "coqtop -ideslave -main-channel stdfds -I ${PEACOQPATH}/plugin -Q ${PEACOQPATH}/plugin PeaCoq"
}
END

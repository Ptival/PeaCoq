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
if [[ `coqtop -v` != *"version 8.5"* ]]; then missing "coqtop version 8.5"; fi
ghc --version   >/dev/null 2>&1 || missing "ghc"
ocamlc -v       >/dev/null 2>&1 || missing "ocaml"

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

log "Cleaning up Haskell packages (reverse order)"
ghc-pkg unregister peacoq-server || true
ghc-pkg unregister peacoqtop || true

log "Building OCaml plugin (needed by peacoqtop's tests)"
(
set -euv
cd peacoqtop/plugin
make -B
)

log "Building and installing peacoqtop"
(
set -euv
cd peacoqtop
log "Dependencies"
cabal install --only-dependencies --enable-tests ${CABALFLAGS}
log "Configure"
cabal configure --enable-tests ${CABALFLAGS}
log "Build"
cabal build -j2
log "Copy and register"
cabal copy
cabal register
)

log "Building and installing peacoq-server"
(
set -euv
cd peacoq-server
log "Dependencies"
cabal install --only-dependencies --enable-tests ${CABALFLAGS}
log "Configure"
cabal configure --enable-tests ${CABALFLAGS}
log "Dependencies"
cabal build -j2
log "Copy and register"
cabal copy
cabal register
)

# this path is ridiculous!
log "Symbolically linking peacoq-server to peacoq"
ln -sf peacoq-server/dist/build/peacoq-server/peacoq-server peacoq

(
set -euv
cd web
log "Installing npm dependencies"
npm install
cd js/peacoq-ts/
log "Installing typings"
./typings-bin prune
./typings-bin install
log "Transpiling front-end"
./tsc -p .
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
, configCoqtop = "coqtop -ideslave -main-channel stdfds -I ${PEACOQPATH}/peacoqtop/plugin -Q ${PEACOQPATH}/peacoqtop/plugin PeaCoq"
}
END


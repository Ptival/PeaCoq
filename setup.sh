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

if [ -f /etc/NIXOS ]; then
  if [ -z "${NIXSHELL+x}" ]; then
    ./scripts/clone-snap.sh
    log "This seems to be NixOS, use nix-shell before calling setup.sh or set NIXSHELL"
    exit 1
  fi
  # This should go elsewhere, to be called if zlib fails to build
  #  INCLUDEDIR=`echo ${NIX_CFLAGS_COMPILE} | grep -o '/nix/store\S*zlib\S*/include' | head -1`
  #  echo "Setting --extra-include-dirs to: ${INCLUDEDIR}"
  #  LIBDIR=`echo ${NIX_LDFLAGS} | grep -o '/nix/store\S*zlib\S*[0-9]/lib' | head -1`
  #  echo "Setting --extra-lib-dirs to: ${LIBDIR}"
  #  CABALFLAGS="--extra-include-dirs=${INCLUDEDIR} --extra-lib-dirs=${LIBDIR}"
else
  cabal --version >/dev/null 2>&1 || missing "cabal-install"
  # camlp5 -v       >/dev/null 2>&1 || missing "camlp5"
  coqc -v         >/dev/null 2>&1 || missing "coq"
  if [[ `coqtop -v` != *"version 8.5"* ]]; then missing "coqtop version 8.5"; fi
  ghc --version   >/dev/null 2>&1 || missing "ghc"
  ocamlc -v       >/dev/null 2>&1 || missing "ocaml"
  log "Cleaning up Haskell packages (reverse order)"
  ghc-pkg unregister peacoq-server || true
  ghc-pkg unregister peacoqtop || true
  log "Building OCaml plugin (needed by peacoqtop's tests)"
  ./setup-peacoq-plugin.sh
  log "Building and installing peacoqtop"
  ./setup-peacoqtop.sh
  log "Building and installing peacoq-server"
  ./scripts/setup-peacoq-server.sh
fi

log "Installing front-end dependencies"
./scripts/frontend-setup.sh

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
{ configUserId = "peacoq"
, configLogPath = "${LOGPATH}"
, configCoqtop = "/home/ptival/coq-serapi/sertop.native --prelude /home/ptival/coq-for-coq-serapi --printer=sertop"
}
END

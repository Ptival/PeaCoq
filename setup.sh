#!/usr/bin/env bash
set -euv

function missing {
  echo >&2 "$1 is missing. Please install it."
  exit 1
}

function log {
  echo -e "\n\nPEACOQ: $1\n\n"
}

function check-and-clone {
  if [ ! -d $1/.git ]; then
    if [ -d /home/ptival ]; then
      git clone git@github.com:Ptival/$1.git
    else
      git clone https://github.com/Ptival/$1.git
    fi
  fi
  (cd $1 && git pull) || exit 1
}

check-and-clone "peacoq-server"

if [ -f /etc/NIXOS ] || [ ! -z "${NIXSHELL+x}" ]; then
  # should change this test to something portable, like testing for peacoq-server
  if [ -z "${NIXSHELL+x}" ]; then
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
  cabal --version || missing "cabal-install"
  # camlp5 -v || missing "camlp5"
  coqc -v || missing "coq"
  coqtop -v || missing "coqtop"
  ghc --version || missing "ghc"
  eval `opam config env`
  ocamlc -v || missing "ocaml"
  log "Cleaning up Haskell packages (reverse order)"
  ghc-pkg unregister peacoq-server || true
  ghc-pkg unregister peacoqtop || true
fi

check-and-clone "peacoq-plugin"
./scripts/setup-coq.sh
./scripts/setup-coq-serapi.sh
(PATH=../coq/bin:$PATH && cd peacoq-plugin && make clean && make)

log "Installing front-end dependencies"
./scripts/setup-frontend.sh

log "Setting up configuration file"
./scripts/setup-configuration.sh

#!/usr/bin/env bash
set -euv

function log {
  echo -e "\n\nPEACOQ: $1\n\n"
}

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

log "Installing front-end dependencies"
./setup-frontend.sh

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

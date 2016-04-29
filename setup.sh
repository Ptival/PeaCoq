#!/usr/bin/env bash
set -eu -o pipefail

function missing {
  echo >&2 "$1 is missing. Please install it."
  echo >&2 "If you are running NixOS, run nix-shell."
  exit 1
}

cabal --version >/dev/null 2>&1 || missing "cabal-install"
camlp5 -v       >/dev/null 2>&1 || missing "camlp5"
coqc -v         >/dev/null 2>&1 || missing "coq"
ocamlc -v       >/dev/null 2>&1 || missing "ocaml"

if [ -d "${HOME}/.nix-profile" ]; then
  CABALFLAGS="--extra-include-dirs=${HOME}/.nix-profile/include --extra-lib-dirs=${HOME}/.nix-profile/lib"
else
  CABALFLAGS=""
fi
cabal install --only-dependencies ${CABALFLAGS}
cabal configure
cabal build

( cd plugin
  make clean && make
)

( cd web
  npm install
  ./node_modules/bower/bin/bower install
  cd js/peacoq-ts/
  ../../node_modules/typings/dist/bin.js install
  ../../node_modules/typescript/bin/tsc -p .
)

# TODO: the config file should not go in HOME, it's annoying for everyone
# TODO: this config should be shared with the Haskell code somehow

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

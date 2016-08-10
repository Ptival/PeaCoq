#!/usr/bin/env bash
set -euv

PKGMGR="brew"

$PKGMGR update

# Haskell server
$PKGMGR install cabal-install ghc
cabal update
cabal install alex happy

# Coq and OCaml plugin
$PKGMGR install ocaml camlp5 opam
# Brew packages a version of coq that was not built with its version of
# ocaml so coq complains
(
git clone https://github.com/coq/coq.git
cd coq
./configure -local
make -j2
make install
) || exit 1

(
git clone https://github.com/ejgallego/coq-serapi.git
cd coq-serapi
BEFORE="/home/egallego/external/coq-git/"
AFTER="$TRAVIS_BUILD_DIR/coq/"
sed -i 's~$BEFORE~$AFTER~g' myocamlbuild.ml
cat myocamlbuild.ml
./configure -local && make -j2
) || exit 1

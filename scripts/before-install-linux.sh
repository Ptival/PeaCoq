#!/usr/bin/env bash
set -euv

(
mkdir -p opam
OPAMINSTALLER="https://raw.github.com/ocaml/opam/master/shell/opam_installer.sh"
wget $OPAMINSTALLER -O - | sh -s $TRAVIS_BUILD_DIR/opam
) || exit 1

export PATH=$TRAVIS_BUILD_DIR/opam:$PATH
opam switch 4.02.3
eval `opam config env`
yes '' | opam install camlp5 ocamlfind ppx_import cmdliner core_kernel sexplib ppx_sexp_conv

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

#!/usr/bin/env bash
set -euv

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

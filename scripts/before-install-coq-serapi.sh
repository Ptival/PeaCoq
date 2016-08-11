#!/usr/bin/env bash
set -euv

git clone https://github.com/ejgallego/coq-serapi.git
cd coq-serapi
git pull
sed -i "s|/home/egallego/external/coq-git/|$TRAVIS_BUILD_DIR/coq/|g" myocamlbuild.ml
make || make clean && make

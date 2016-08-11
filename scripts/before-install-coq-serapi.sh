#!/usr/bin/env bash
set -euv

if [ ! -f coq/.git/config ]; then
  git clone https://github.com/ejgallego/coq-serapi.git
fi
cd coq-serapi
git pull
sed --in-place=.bak "s|/home/egallego/external/coq-git/|$TRAVIS_BUILD_DIR/coq/|g" myocamlbuild.ml
make || make clean && make

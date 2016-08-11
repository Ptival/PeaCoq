#!/usr/bin/env bash
set -euv

if [ ! -f coq/.git/config ]; then
  git clone https://github.com/ejgallego/coq-serapi.git
fi
cd coq-serapi
git pull
# Holy shit, sed on OSX and on Linux are really hard to make work the same...
sed -i.bak "s|/home/egallego/external/coq-git/|$TRAVIS_BUILD_DIR/coq/|g" myocamlbuild.ml
make || make clean && make

#!/usr/bin/env bash
set -euv

if [ ! -d coq-serapi/.git ]; then
  git clone https://github.com/ejgallego/coq-serapi.git
fi
cd coq-serapi
git checkout myocamlbuild.ml # undo the effects of sed
git pull
# Holy shit, sed on OSX and on Linux are really hard to make work the same...
sed -i.bak "s|/home/egallego/external/coq-git/|$PWD/../coq/|g" myocamlbuild.ml
make clean && COQBIN="../coq/bin" make

#!/usr/bin/env bash
set -euv

branch="v8.9"

if [ ! -d coq-serapi/.git ]; then
  git clone https://github.com/ejgallego/coq-serapi.git
fi
cd coq-serapi
git fetch origin $branch
git checkout $branch
# Slower:
# SERAPI_COQ_HOME="$PWD/../coq/" COQBIN="../coq/bin" (make clean; make)
#SERAPI_COQ_HOME="$PWD/../coq/" COQBIN="../coq/bin" make build
make build
#OCAMLPATH=$OCAMLPATH SERAPI_COQ_HOME="$PWD/../coq/" COQBIN="../coq/bin" make sertop

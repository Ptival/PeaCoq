#!/usr/bin/env bash
set -euv

cd peacoqtop/plugin
eval `opam config env`
ocamlc -v
make -B

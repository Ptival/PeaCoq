#!/usr/bin/env bash
set -euv

cd peacoq-plugin
eval `opam config env`
ocamlc -v
make -B

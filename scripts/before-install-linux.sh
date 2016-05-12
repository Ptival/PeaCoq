#!/usr/bin/env bash
set -euv

COQ="coq-8.5pl1"

# Coq and OCaml plugin
# Trusty packages 8.4, so we need to install manually?
if [ ! -d "$HOME/$COQ" ]; then
  wget https://coq.inria.fr/distrib/V8.5pl1/files/$COQ.tar.gz
  tar -xzvf $COQ.tar.gz
  ( cd $COQ
    ./configure -local
    make -j2
    make install
  ) || exit 1
else
  echo "Using coq from cache"
fi

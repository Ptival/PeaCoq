#!/usr/bin/env bash
set -euv

# Coq and OCaml plugin
# Trusty packages 8.4, so we need to install manually?
if [ ! -f "$TRAVIS_BUILD_DIR/coq-$COQVER/bin/coqc" ]; then
  wget https://coq.inria.fr/distrib/V$COQVER/files/coq-$COQVER.tar.gz
  tar -xzvf coq-$COQVER.tar.gz
  ( cd coq-$COQVER
    ./configure -local
    make -j2
    make install
  ) || exit 1
else
  echo "Using coq from cache"
fi


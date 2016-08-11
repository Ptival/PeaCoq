#!/usr/bin/env bash
set -euv

if [ ! -f coq/.git/config ]; then
  git clone https://github.com/coq/coq.git
fi
cd coq
git pull
./configure -local
make -j2 || make clean && make -j2
make install

#!/usr/bin/env bash
set -euv

if [ ! -d coq ]; then
  git clone https://github.com/coq/coq.git
fi
cd coq
ls
git pull
./configure -local
make -j2 || make clean && make -j2
make install

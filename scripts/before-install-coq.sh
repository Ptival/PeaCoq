#!/usr/bin/env bash
set -euv

git clone https://github.com/coq/coq.git
cd coq
git pull
./configure -local
make -j2 || make clean && make -j2
make install

#!/usr/bin/env bash
set -euv

if [ ! -d coq/.git ]; then
  git clone https://github.com/coq/coq.git
fi
cd coq
git pull
if [ ! -f config/Makefile ]; then
  ./configure -local
fi
make -j2 || make clean && make -j2
make install

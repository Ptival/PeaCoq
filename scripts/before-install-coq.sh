#!/usr/bin/env bash
set -euv

pwd
if [ ! -d coq ]; then
  git clone https://github.com/coq/coq.git
fi
cd coq
pwd
ls
git pull
sh ./configure -local
make -j2 || make clean && make -j2
make install

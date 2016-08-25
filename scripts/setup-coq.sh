#!/usr/bin/env bash
set -euv

branch="trunk"
commit="7382758"

if [ ! -d coq/.git ]; then
  git clone https://github.com/coq/coq.git
fi
cd coq
git pull origin $branch
git checkout $commit
if [ ! -f config/Makefile ]; then
  ./configure -local
fi
make -j2 || make clean && make -j2
make install

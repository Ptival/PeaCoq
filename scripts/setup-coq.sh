#!/usr/bin/env bash
set -euv

branch="v8.6"
commit="f1a561d847e207433a0ec3e6333798dfa19e4a0c"

if [ ! -d coq/.git ]; then
  git clone https://github.com/coq/coq.git
fi
cd coq
git fetch origin $branch
git checkout $commit
if [ ! -f config/Makefile ]; then
  ./configure -local
fi
make -j$(nproc) || make clean && make -j$(nproc)
make install

#!/usr/bin/env bash
set -euv

mkdir -p snap-framework
cd snap-framework
for p in io-streams-haproxy heist snap-core snap-server snap; do
  if [ ! -d ${p} ]; then
    git clone https://github.com/Ptival/${p}.git
  fi
  (
  cd ${p}
  # if only there was a way of saying "install if more recent than current"
  cabal install || true
  )
done

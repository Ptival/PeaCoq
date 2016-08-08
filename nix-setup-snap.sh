#!/usr/bin/env bash
set -euv

mkdir -p snap-framework
cd snap-framework
for p in heist io-streams-haproxy snap snap-core snap-server xmlhtml; do
  if [ ! -d ${p} ]; then
    git clone https://github.com/Ptival/${p}.git
  fi
done


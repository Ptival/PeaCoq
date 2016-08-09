#!/usr/bin/env bash
set -euv

. shared-variables.sh

mkdir -p snap-framework
cd snap-framework

for p in ${CABALPACKAGES}; do
  if [ ! -d ${p} ]; then
    git clone https://github.com/Ptival/${p}.git
  fi
done


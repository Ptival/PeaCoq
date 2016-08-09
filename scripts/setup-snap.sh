#!/usr/bin/env bash
set -euv

. shared-variables.sh

cd snap-framework

for p in ${CABALPACKAGES}; do
  (
  cd ${p}
  # if only there was a way of saying "install if more recent than current"
  cabal install || true
  )
done


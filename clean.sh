#!/usr/bin/env bash
set -euv

(cd peacoqtop        && cabal clean)
(cd peacoq-server    && cabal clean)
(cd peacoqtop/plugin && make clean)
(
set -euv
cd web
rm -rf node_modules
cd js
rm -rf peacoq-js-of-ts
cd peacoq-ts
rm -rf typings
)


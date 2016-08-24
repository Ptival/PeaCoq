#!/usr/bin/env bash
set -euv

cd web

npm --version
npm install

(
cd node_modules
./requirejs/bin/r.js -convert s-expression s-expression-amd
)

cd ts

./typings-bin prune
./typings-bin install

rm -rf ../js-of-ts
./tsc -p . --listFiles --diagnostics

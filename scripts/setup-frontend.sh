#!/usr/bin/env bash
set -euv

cd web

npm --version
npm install

(
cd node_modules
./requirejs/bin/r.js -convert s-expression s-expression-amd
)

./typings prune
./typings install

rm -rf ./js-of-ts
./tsc -p . --diagnostics
./tslint --project .

#!/usr/bin/env bash
set -euv

cd web

npm --version
# This won't install correctly with newest npm? (cf. peer dependencies)
npm install typescript@2.1.0-dev.20160915 tslint
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

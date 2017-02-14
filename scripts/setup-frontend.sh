#!/usr/bin/env bash
set -euv

cd web

npm --version
npm prune
# This won't install correctly with newest npm? (cf. peer dependencies)
#npm install typescript@2.0.6 || true # fails often on Travis...
#npm install tslint || true # also fails often on Travis...
npm install

(
cd node_modules
./requirejs/bin/r.js -convert s-expression s-expression-amd
)

rm -rf ./js-of-ts
./tsc -p . --diagnostics
./tslint --project .

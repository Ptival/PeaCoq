#!/usr/bin/env bash
set -euv

cd web

npm install

(
cd node_modules
./requirejs/bin/r.js -convert s-expression s-expression-amd
)

cd js/peacoq-ts/

./typings-bin prune
./typings-bin install

rm -rf ../peacoq-js-of-ts/*
./tsc -p .


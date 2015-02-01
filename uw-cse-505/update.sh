#!/usr/bin/env bash

cd $HOME/PeaCoq
git pull
./setup.sh
cabal install

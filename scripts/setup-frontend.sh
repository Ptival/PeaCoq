#!/usr/bin/env bash
set -euv

(
  cd peacoq-frontend
  ./setup.sh
) || exit 1

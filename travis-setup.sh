#!/usr/bin/env bash
set -euv

# cabal sometimes take too long without outputting anything
./setup.sh &

MINUTES=0
LIMIT=30
while kill -0 $! >/dev/null 2>&1; do
  echo -n -e " \b" # invisible!
  if [ $MINUTES == $LIMIT ]; then
    break;
  fi
  MINUTES=$((MINUTES+1))
  sleep 60
done

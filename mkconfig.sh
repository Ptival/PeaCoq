#!/usr/bin/env bash

USER=$(whoami)
TMP="/tmp/"
COQTOP=$(which coqtop)

cat << EOF > ~/.PeaCoqConfig.hs
PeaCoqConfig
{ configUserId  = "$USER"
, configLogPath = "$TMP"
, configCoqtop = "$COQTOP -ideslave"
}
EOF

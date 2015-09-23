#!/usr/bin/env bash

CONFIGPATH="$HOME"
PEACOQCONFIG=".PeaCoqConfig.hs"
USER="$USER"
TMP="/tmp/"
COQTOP=$(which coqtop)

cat << EOF > "$HOME/$PEACOQCONFIG"
PeaCoqConfig
{ configUserId  = "$USER"
, configLogPath = "$TMP"
, configCoqtop = "$COQTOP -ideslave"
}
EOF

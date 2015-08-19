#!/usr/bin/env bash

HOME=$(echo ~)
CONFIGPATH="${HOME}"
LOGPATH="${HOME}/PeaCoq/logs"
PEACOQCONFIG=".PeaCoqConfig.hs"

if [ "$#" -ne 2 ]
then
  echo "Usage: $0 USERID PORT"
  exit 1
fi

USERID="$1"
PORT="$2"

echo -e "PeaCoqConfig {\nconfigUserId  = \"${USERID}\",\nconfigLogPath = \"${LOGPATH}\",\nconfigCoqtop = \"coqtop -ideslave\"\n}" > "${CONFIGPATH}/${PEACOQCONFIG}"

peacoq -p "$PORT"


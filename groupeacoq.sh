#!/usr/bin/env bash

HOME=$(echo ~)
CONFIGPATH="${HOME}"
LOGPATH="${HOME}/PeaCoq/logs"
PEACOQCONFIG=".PeaCoqConfig.hs"
STUDYID="group$1"

if [ "$#" -ne 1 ]
then
  echo "Usage: $0 GROUPNUMBER"
  exit 1
fi

echo "PeaCoqConfig { configUserId  = Just \"${STUDYID}\", configLogPath = \"${LOGPATH}\" }" > "${CONFIGPATH}/${PEACOQCONFIG}"

peacoq -p "425$1"


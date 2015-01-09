#!/usr/bin/env bash

ZACHHOME=$(echo ~ztatlock)
CONFIGPATH="${HOME}"
LOGPATH="${ZACHHOME}/PeaCoq/logs/"
USERNAME=$(whoami)
PEACOQCONFIG=".PeaCoqConfig.hs"

export PATH="~ztatlock/.cabal/bin:~ztatlock/local/bin:$PATH"

case "$1" in
    "nolog")
        echo "PeaCoqConfig { configUserId  = Nothing, configLogPath = \"${LOGPATH}\" }" > "${CONFIGPATH}/${PEACOQCONFIG}"
        ;;
    *)
        STUDYID=$(echo -n "${USERNAME}" | md5sum | awk '{print $1}')
        echo "PeaCoqConfig { configUserId  = Just \"${STUDYID}\", configLogPath = \"${LOGPATH}\" }" > "${CONFIGPATH}/${PEACOQCONFIG}"
        ;;
esac

cd "${ZACHOME}/PeaCoq/"

peacoq &

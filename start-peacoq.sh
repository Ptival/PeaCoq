#!/usr/bin/env bash

ZACHHOME=$(echo ~ztatlock)
CONFIGPATH="${HOME}"
LOGPATH="${ZACHHOME}/PeaCoq/logs/"
USERNAME=$(whoami)
PEACOQCONFIG=".PeaCoqConfig.hs"

export PATH="${ZACHHOME}/.cabal/bin:${ZACHHOME}/local/bin:$PATH"

case "$1" in
    "nolog")
        echo "PeaCoqConfig { configUserId  = Nothing, configLogPath = \"${LOGPATH}\" }" > "${CONFIGPATH}/${PEACOQCONFIG}"
        ;;
    *)
        STUDYID=$(echo -n "${USERNAME}" | md5sum | awk '{print $1}')
        echo "PeaCoqConfig { configUserId  = Just \"${STUDYID}\", configLogPath = \"${LOGPATH}\" }" > "${CONFIGPATH}/${PEACOQCONFIG}"
        ;;
esac

pushd "${ZACHHOME}/PeaCoq/" > /dev/null

peacoq 2>/dev/null &

popd > /dev/null

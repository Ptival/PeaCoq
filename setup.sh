#!/usr/bin/env bash
set -eu -o pipefail

PEACOQPATH=`pwd`
CONFIGPATH="${HOME}"
PEACOQCONFIG=".PeaCoqConfig.hs"
FILE="${CONFIGPATH}/${PEACOQCONFIG}"
LOGPATH="/tmp"

cat <<END > ${FILE}
PeaCoqConfig
{ configUserId = ""
, configLogPath = "${LOGPATH}"
, configCoqtop = "coqtop -ideslave -main-channel stdfds -I ${PEACOQPATH}/plugin -Q ${PEACOQPATH}/plugin PeaCoq"
}
END


# TODO: the config file should not go in HOME, it's annoying for everyone
# TODO: this config should be shared with the Haskell code somehow

peacoqpath=`pwd`
configpath="$HOME"
peacoqconfig=".PeaCoqConfig.hs"
file="$configpath/$peacoqconfig"
logpath="/tmp"

cat <<END > $file
PeaCoqConfig
{ configUserId     = "peacoq"
, configLogPath    = "$logpath"
, configSertop     = "$peacoqpath/coq-serapi/sertop.native --printer=sertop -I $peacoqpath/peacoq-plugin -Q $peacoqpath/peacoq-plugin,PeaCoq"
, configDirToServe = "web/"
}
END

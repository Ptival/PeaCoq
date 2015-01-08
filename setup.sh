#!/bin/sh -e

MKDIR="mkdir -p"
GET="wget -O - "
LN="ln -sf"

cd web/

$MKDIR bootstrap
cd bootstrap/
$GET https://github.com/twbs/bootstrap/releases/download/v3.3.1/bootstrap-3.3.1-dist.zip > bootstrap-3.3.1-dist.zip
unzip -o bootstrap-3.3.1-dist.zip
cd ..
$LN bootstrap/dist/js/bootstrap.min.js bootstrap.js
$LN bootstrap/dist/css/bootstrap.min.css bootstrap.css
$LN bootstrap/dist/css/bootstrap-theme.min.css bootstrap-theme.css
$LN bootstrap/dist/fonts fonts

$MKDIR d3
cd d3
$GET https://github.com/mbostock/d3/releases/download/v3.4.13/d3.zip > d3.zip
unzip -o d3.zip
cd ..
$LN d3/d3.min.js d3.js

$MKDIR jquery
cd jquery/
$GET http://code.jquery.com/jquery-1.11.1.min.js > jquery-1.11.1.min.js
cd ..
$LN jquery/jquery-1.11.1.min.js jquery.js

$MKDIR lodash
cd lodash/
$GET https://raw.github.com/lodash/lodash/2.4.1/dist/lodash.min.js > lodash.min.js
cd ..
$LN lodash/lodash.min.js lodash.js

$MKDIR rangy
cd rangy/
$GET https://rangy.googlecode.com/svn/trunk/currentrelease/uncompressed/rangy-core.js > rangy-core.js
$GET https://rangy.googlecode.com/svn/trunk/src/js/modules/rangy-textrange.js > rangy-textrange.js
cd ..
$LN rangy/rangy-core.js rangy-core.js
$LN rangy/rangy-textrange.js rangy-textrange.js

$MKDIR highlight
cd highlight/
$GET https://raw.githubusercontent.com/highlightjs/cdn-release/master/build/highlight.min.js > highlight.min.js
$GET https://raw.githubusercontent.com/highlightjs/cdn-release/master/build/languages/ocaml.min.js > ocaml.min.js
$GET https://raw.githubusercontent.com/highlightjs/cdn-release/master/build/styles/github.min.css > github.min.css
cd ..
$LN highlight/highlight.min.js highlight.js
$LN highlight/ocaml.min.js ocaml.js
$LN highlight/github.min.css highlight.css

cd ..

if [ "$#" -eq 1 ]; then
    echo "Config { configUserId  = Just \"$1\", configLogPath = \".\" }" > config.hs
fi

if [ "$#" -eq 2 ]; then
    echo "Config { configUserId  = Just \"$1\", configLogPath = \"$2\" }" > config.hs
fi

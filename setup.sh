#!/bin/sh -e

cd web/

if [ ! -f bootstrap.js ]; then
    mkdir -p bootstrap
    cd bootstrap/
    wget https://github.com/twbs/bootstrap/releases/download/v3.3.1/bootstrap-3.3.1-dist.zip
    unzip bootstrap-3.3.1-dist.zip
    cd ..
    ln -s bootstrap/dist/js/bootstrap.min.js bootstrap.js
    ln -s bootstrap/dist/css/bootstrap.min.css bootstrap.css
    ln -s bootstrap/dist/css/bootstrap-theme.min.css bootstrap-theme.css
    ln -s bootstrap/dist/fonts fonts
fi

if [ ! -f d3.js ]; then
    mkdir -p d3
    cd d3
    wget https://github.com/mbostock/d3/releases/download/v3.4.13/d3.zip
    unzip d3.zip
    cd ..
    ln -s d3/d3.min.js d3.js
fi

if [ ! -f jquery.js ]; then
    mkdir -p jquery
    cd jquery/
    wget http://code.jquery.com/jquery-1.11.1.min.js
    cd ..
    ln -s jquery/jquery-1.11.1.min.js jquery.js
fi

if [ ! -f lodash.js ]; then
    mkdir -p lodash
    cd lodash/
    wget https://raw.github.com/lodash/lodash/2.4.1/dist/lodash.min.js
    cd ..
    ln -s lodash/lodash.min.js lodash.js
fi

if [ ! -f rangy-core.js ]; then
    mkdir -p rangy
    cd rangy/
    wget https://cdnjs.cloudflare.com/ajax/libs/rangy/1.2.3/rangy-core.js
    cd ..
    ln -s rangy/rangy-core.js rangy-core.js
fi

if [ ! -f highlight.js ]; then
    mkdir -p highlight
    cd highlight/
    wget https://raw.githubusercontent.com/highlightjs/cdn-release/master/build/highlight.min.js
    wget https://raw.githubusercontent.com/highlightjs/cdn-release/master/build/languages/ocaml.min.js
    wget https://raw.githubusercontent.com/highlightjs/cdn-release/master/build/styles/github.min.css
    cd ..
    ln -s highlight/highlight.min.js highlight.js
    ln -s highlight/ocaml.min.js ocaml.js
    ln -s highlight/github.min.css highlight.css
fi

cd ..

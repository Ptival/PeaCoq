#!/bin/sh -e

cd heroku
cp /usr/local/bin/coqtop .
cp /home/vrobert/.cabal/bin/peacoq .
rm -rf web
cp -r /home/vrobert/peacoq/web .
touch requirements.txt
git add libs web coqtop peacoq Procfile requirements.txt
git commit -m "new version"
git push


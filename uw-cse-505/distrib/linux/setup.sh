#!/usr/bin/env bash

VERSION=0.2-alpha
DIR=PeaCoq-${VERSION}
TGZ=v${VERSION}.tar.gz

wget -N https://github.com/Ptival/PeaCoq/archive/v${TGZ}
tar -xzvf ${TGZ}
cd ${DIR}
wget -N https://github.com/Ptival/PeaCoq/releases/download/v0.2-alpha/peacoq
chmod +x peacoq
./setup.sh
cd ..

echo "==========================================="
echo "SETUP COMPLETE"
echo "==========================================="
echo "Now enter directory ${DIR} and run ./peacoq"


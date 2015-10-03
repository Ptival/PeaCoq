#! /bin/sh

docker build -t peacoq .
docker run -t -i -p 4242:4242 peacoq


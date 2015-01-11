#!/usr/bin/env bash

function main {
  D=$(basename $(pwd))
  cat <<HERE
<html>
<head>
  <title>Materials for $D</title>
  <link rel='stylesheet' type='text/css' href='../style.css'>
</head>
<body>
  <h1>Materials for $D</h1>
  <hr>
  <div id='listing'><ul>
HERE
  for f in *; do
    case "$f" in
      "materials.html"|*.glob|*.vo|"coqdoc.css")
        continue
        ;;
    esac
    echo "    <li><a href='$f'>$f</a></li>"
  done
  cat <<HERE
  </ul>
  <p><a href='..'>505 Main</a></p>
  </div>
</body>
</html>
HERE
}

if [ -d "$1" ]; then
  pushd $1 &> /dev/null
  main > materials.html
  popd &> /dev/null
else
  echo "ERROR: '$1' is not an existing directory."
fi

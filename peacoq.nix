{ mkDerivation, adjunctions, aeson, array, base, bytestring
, conduit, conduit-extra, containers, data-default, directory
, exceptions, filemanip, hslogger, lens, MissingH, monad-loops, mtl
, network, process, random, snap, snap-core, snap-server, stdenv
, tagsoup, text, time, transformers, unordered-containers
, utf8-string, xml-conduit, xml-types
}:
mkDerivation {
  pname = "peacoq";
  version = "0.1";
  src = ./.;
  isLibrary = false;
  isExecutable = true;
  executableHaskellDepends = [
    adjunctions aeson array base bytestring conduit conduit-extra
    containers data-default directory exceptions filemanip hslogger
    lens MissingH monad-loops mtl network process random snap snap-core
    snap-server tagsoup text time transformers unordered-containers
    utf8-string xml-conduit xml-types
  ];
  description = "PeaCoq is a web front-end to Coq";
  license = stdenv.lib.licenses.mit;
}

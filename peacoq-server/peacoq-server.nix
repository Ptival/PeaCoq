{ mkDerivation, adjunctions, aeson, base, bytestring, containers
, directory, hslogger, lens, MissingH, monad-loops, mtl, network
, process, random, snap, snap-core, snap-server, stdenv, text, time
, transformers, unordered-containers, utf8-string, zlib, zlibStatic
}:
mkDerivation {
  pname = "peacoq-server";
  version = "0.1";
  src = ./.;
  isLibrary = true;
  isExecutable = true;
  libraryHaskellDepends = [
    adjunctions aeson base bytestring containers directory hslogger
    lens MissingH monad-loops mtl network process random snap snap-core
    snap-server text time transformers unordered-containers utf8-string
    zlib zlibStatic
  ];
  librarySystemDepends = [ zlib zlibStatic ];
  executableHaskellDepends = [ base zlib zlibStatic ];
  executableSystemDepends = [ zlib zlibStatic ];
  testHaskellDepends = [ base zlib zlibStatic ];
  description = "Server to bridge a web interface to coqtop";
  license = stdenv.lib.licenses.mit;
}

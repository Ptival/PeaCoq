{ mkDerivation, aeson, base, bytestring, conduit, conduit-extra
, containers, exceptions, HUnit, monad-loops, mtl, process, stdenv
, tagsoup, text, transformers, xml-conduit, xml-types, zlib
}:
mkDerivation {
  pname = "peacoqtop";
  version = "0.1";
  src = ./.;
  isLibrary = true;
  isExecutable = true;
  libraryHaskellDepends = [
    aeson base bytestring conduit conduit-extra containers exceptions
    monad-loops mtl process tagsoup text transformers xml-conduit
    xml-types
  ];
  librarySystemDepends = [ zlib ];
  executableHaskellDepends = [ base ];
  executableSystemDepends = [ zlib ];
  testHaskellDepends = [ base HUnit monad-loops mtl process ];
  description = "Wrapper around coqtop using by PeaCoq";
  license = stdenv.lib.licenses.mit;
}

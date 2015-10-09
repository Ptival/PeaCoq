{ nixpkgs ? import <nixpkgs> {}, compiler ? "default" }:

let

  inherit (nixpkgs) pkgs;

  f = { mkDerivation, adjunctions, aeson, array, base, bytestring
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
        license = stdenv.lib.licenses.unfree;
      };

  haskellPackages = if compiler == "default"
                       then pkgs.haskellPackages
                       else pkgs.haskell.packages.${compiler};

  drv = haskellPackages.callPackage f {};

in

  if pkgs.lib.inNixShell then drv.env else drv

{ nixpkgs ? import <nixpkgs> {}, compiler ? "default" }:

let

  inherit (nixpkgs) pkgs;

  f = { mkDerivation, aeson, alex, array, base, bytestring, conduit
      , conduit-extra, containers, data-default, directory, exceptions
      , filemanip, happy, hslogger, lens, MissingH, network, process
      , random, snap, snap-core, snap-extras, snap-server, stdenv
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
          aeson array base bytestring conduit conduit-extra containers
          data-default directory exceptions filemanip hslogger lens MissingH
          network process random snap snap-core snap-extras snap-server
          tagsoup text time transformers unordered-containers utf8-string
          xml-conduit xml-types
        ];
        executableToolDepends = [ alex happy ];
        description = "PeaCoq is a web front-end to Coq";
        license = stdenv.lib.licenses.bsd3;
      };

  haskellPackages = if compiler == "default"
                       then pkgs.haskellPackages
                       else pkgs.haskell.packages.${compiler};

  drv = haskellPackages.callPackage f {};

in

  if pkgs.lib.inNixShell then drv.env else drv

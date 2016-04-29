{ nixpkgs ? import <nixpkgs> {}, compiler ? "ghc7103" }:
nixpkgs.lib.overrideDerivation
  (import ./default.nix { inherit nixpkgs compiler; }).env
  (old:
    { buildInputs = old.buildInputs ++ (with nixpkgs; [
        cabal-install
        coq_8_5
        ghc
        ocaml_4_02
        ocamlPackages.camlp5_6_strict
        nodejs-5_x
        zlib
      ]);
    }
  )

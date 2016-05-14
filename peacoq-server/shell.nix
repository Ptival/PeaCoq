{ nixpkgs ? import <nixpkgs> {}, compiler ? "ghc7103" }:
nixpkgs.lib.overrideDerivation
  (import ./default.nix { inherit nixpkgs compiler; }).env
  (old:
    { buildInputs = old.buildInputs ++ (with nixpkgs; [
        cabal-install
        coq_8_5
        ghc
        ocaml # need 4.0.1 to work with camlp5
        ocamlPackages.camlp5_6_strict
        nodejs-5_x
        zlib
      ]);
      nativeBuildInputs = old.nativeBuildInputs ++ (with nixpkgs; [
        zlib
      ]);
    }
  )

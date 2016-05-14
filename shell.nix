{ nixpkgs ? import <nixpkgs> {}, compiler ? "ghc7103" }:
nixpkgs.stdenv.mkDerivation {
  name = "peacoq";
  buildInputs = (with nixpkgs; [
    cabal-install
    coq_8_5
    ghc
    ocaml # need 4.0.1 to work with camlp5
    ocamlPackages.camlp5_6_strict
    nodejs-5_x
    zlib
  ]);
  nativeBuildInputs = (with nixpkgs; [
    zlib
  ]);
}


{ nixpkgs ? import <nixpkgs> {}, compiler ? "ghc7103" }:
let drv = nixpkgs.pkgs.haskell.packages.${compiler}.callPackage ./peacoq.nix {}; in
drv.overrideDerivation (
  attrs:
    with nixpkgs;
    { propagatedBuildInputs =
        attrs.propagatedBuildInputs ++ [
          coq_8_5
          ocaml
          ocamlPackages.camlp5_6_strict
        ];
    }
)

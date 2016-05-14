{ nixpkgs ? import <nixpkgs> {}, compiler ? "ghc7103" }:
nixpkgs.pkgs.haskell.packages.${compiler}.callPackage ./peacoqtop.nix {}

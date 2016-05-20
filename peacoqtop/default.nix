{ nixpkgs ? import <nixpkgs> {}, compiler ? "ghc7103" }:
let peacoqtop =
  nixpkgs.pkgs.haskell.packages.${compiler}.callPackage ./peacoqtop.nix {};
in
nixpkgs.lib.overrideDerivation peacoqtop (old:
  { buildInputs = old.buildInputs ++ (with nixpkgs; [
      coq_8_5
    ]);
    shellHook = '' export NIXSHELL="$NIXSHELL\[peacoqtop\]" '';
  }
)


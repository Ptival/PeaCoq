{ nixpkgs ? import <nixpkgs> {}
, compiler ? "ghc7103"
, peacoqtop
}:
let peacoq-server =
  nixpkgs.pkgs.haskell.packages.${compiler}.callPackage ./peacoq-server.nix { peacoqtop = peacoqtop; };
in
nixpkgs.lib.overrideDerivation peacoqtop (old:
  { buildInputs = old.buildInputs ++ (with nixpkgs; [
      # doesn't need anything?
    ]);
    shellHook = '' export NIXSHELL="$NIXSHELL\[peacoq-server\]" '';
  }
)


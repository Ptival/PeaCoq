{ nixpkgs ? import <nixpkgs> {}
, compiler ? "ghc7103"
}:
let peacoqtop = (import ../peacoqtop/default.nix { inherit nixpkgs compiler; }); in
let peacoq-server =
  nixpkgs.pkgs.haskell.packages.${compiler}.callPackage ./peacoq-server.nix { inherit peacoqtop; };
in
nixpkgs.lib.overrideDerivation peacoqtop (old:
  { buildInputs = old.buildInputs ++ (with nixpkgs; [
      # doesn't need anything?
    ]);
    shellHook = '' export NIXSHELL="$NIXSHELL\[peacoq-server\]" '';
  }
)


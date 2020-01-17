{ nixpkgs ? import ~/nixpkgs {}
}:
nixpkgs.ocamlPackages.callPackage ./coq-serapi/default.nix {}

{ nixpkgs  ? import <nixpkgs> {}
, compiler ? "ghc802"
}:
let
  coq-serapi = nixpkgs.ocamlPackages.callPackage ./coq-serapi/default.nix {};
in
#let callPackage = nixpkgs.pkgs.haskell.packages.${compiler}.callPackage; in
# We call default.nix because it has some overrides
#let peacoq-server = callPackage peacoq-server/default.nix {
#  inherit compiler;
#}; in
nixpkgs.stdenv.mkDerivation {
  name = "peacoq";
  buildInputs = (with nixpkgs; [
    #cabal-install
    coq_8_9
    coq-serapi
    dune
    #ghc
    ocaml
    nodejs-10_x
    #peacoq-server
  ] ++ (with ocamlPackages;
    [
      # Coq:
      camlp5 ocaml findlib
      # CoqIDE:
      lablgtk
      # SerAPI:
      camlp4 cmdliner
      ocamlbuild opam
      ppx_driver ppx_import ppx_sexp_conv
      sexplib
    ])
  );
  nativeBuildInputs = (with nixpkgs; [
  ]);
  shellHook = ''
    export NIXSHELL="$NIXSHELL\[PeaCoq\]"
    export SSL_CERT_FILE="/etc/ssl/certs/ca-bundle.crt"
    echo -e "\nRemember to run setup.sh again\n"
    # ./setup.sh
  '';
}

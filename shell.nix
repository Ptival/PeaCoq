{ nixpkgs ? import <nixpkgs> {}, compiler ? "ghc802" }:
let callPackage = nixpkgs.pkgs.haskell.packages.${compiler}.callPackage; in
let peacoq-server = callPackage peacoq-server/peacoq-server.nix {}; in
nixpkgs.stdenv.mkDerivation {
  name = "peacoq";
  #jailbreak = true;
  buildInputs = (with nixpkgs; [
    ghc
    haskellPackages.zlib
    nodejs
    zlib
    zlibStatic
    peacoq-server
  ] ++ (with ocamlPackages_4_02; [
      # Coq:
      camlp5_6_strict ocaml findlib
      # CoqIDE:
      lablgtk
      # SerAPI:
      camlp4 cmdliner ocamlbuild ppx_import ppx_sexp_conv sexplib
      ocamlbuild opam
    ])
  );
  nativeBuildInputs = (with nixpkgs; [
    zlib
    zlibStatic
  ]);
  shellHook = ''
    export NIXSHELL="$NIXSHELL\[PeaCoq\]"
    export SSL_CERT_FILE="/etc/ssl/certs/ca-bundle.crt"
    echo -e "\nRemember to run setup.sh again\n"
    # ./setup.sh
  '';
}

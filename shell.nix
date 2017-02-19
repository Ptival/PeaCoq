{ nixpkgs ? import <nixpkgs> {}, compiler ? "ghc801" }:
let callPackage = nixpkgs.pkgs.haskell.packages.${compiler}.callPackage; in
#let snapPath = ./peacoq-server/snap-framework; in
#let xmlhtml = callPackage "${snapPath}/xmlhtml/xmlhtml.nix" {}; in
#let heist = callPackage "${snapPath}/heist/heist.nix" { inherit xmlhtml; }; in
#let io-streams-haproxy = callPackage "${snapPath}/io-streams-haproxy/io-streams-haproxy.nix" {}; in
#let snap-core = callPackage "${snapPath}/snap-core/snap-core.nix" {}; in
#let snap-server = callPackage "${snapPath}/snap-server/snap-server.nix" { inherit io-streams-haproxy snap-core; }; in
#let snap = callPackage "${snapPath}/snap/snap.nix" { inherit heist snap-core snap-server; }; in
let peacoq-server = callPackage peacoq-server/peacoq-server.nix {}; in
nixpkgs.stdenv.mkDerivation {
  name = "peacoq";
  jailbreak = true;
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

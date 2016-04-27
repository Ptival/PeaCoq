with import <nixpkgs> {}; {
  peacoqPluginEnv = stdenv.mkDerivation {
    name = "peacoq-plugin";
    buildInputs = [ coq ocaml ocamlPackages.camlp5_6_strict ];
  };
}

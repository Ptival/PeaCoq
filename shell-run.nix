with import <nixpkgs> {}; {
  peacoqPluginEnv = stdenv.mkDerivation {
    name = "peacoq-plugin";
    buildInputs = [ coqPackages_8_5.coq ocaml ocamlPackages.camlp5_6_strict ];
  };
}

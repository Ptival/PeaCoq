with import <nixpkgs> {}; {
  peacoqEnv = stdenv.mkDerivation {
    name = "peacoq";
    buildInputs = [ coq ];
  };
}


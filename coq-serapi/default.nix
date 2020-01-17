{ fetchFromGitHub, lib, stdenv, buildDunePackage, coq_8_9, ocamlPackages }:
buildDunePackage rec {
  pname = "coq-serapi";
  version = "8.9.0+0.6.0";

  minimumOCamlVersion = "4.06";

  src = fetchFromGitHub {
    owner = "ejgallego";
    repo = "coq-serapi";
    rev = "a6b4445d49be123019f9f83ac39b8832b7224a5e";
    sha256 = "1fwk86x5kfrhzj7zfv09nmq15806ywgmagrpz8k5sp7gf0d7axdc";
  };

  buildInputs = with ocamlPackages; [
    camlp5
    cmdliner
    coq_8_9
    ppx_import
    ppx_sexp_conv
    sexplib
  ];

  meta = with stdenv.lib; {
    homepage = https://github.com/ejgallego/coq-serapi;
    description = "SerAPI is a library for machine-to-machine interaction with the Coq proof assistant";
    license = licenses.lgpl21Plus;
    maintainers = [ maintainers.ptival ];
  };
}

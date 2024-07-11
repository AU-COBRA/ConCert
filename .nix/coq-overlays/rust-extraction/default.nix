{ lib, mkCoqDerivation, which, coq
  , metacoq, version ? null }:

with lib; mkCoqDerivation {
  pname = "rust-extraction";
  repo = "coq-rust-extraction";
  owner = "AU-COBRA";
  domain = "github.com";

  inherit version;

  defaultVersion = "dev";
  release."dev".rev       = "026405f82505a20949511fec2884c87495e6e91c";
  release."dev".sha256    = "rBqEBlDCVCr4aJ3qTK1tzWuvuVmDc82odt5vTmdr/5Y=";

  propagatedBuildInputs = [ coq.ocamlPackages.findlib metacoq ];

  patchPhase = ''
    patchShebangs ./process_extraction.sh
    patchShebangs ./tests/process-extraction-examples.sh
  '';

  mlPlugin = true;

  meta = {
    description = "A framework for extracting Coq programs to Rust";
    license = licenses.mit;
  };
}

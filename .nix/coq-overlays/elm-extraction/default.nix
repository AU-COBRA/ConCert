{ lib, mkCoqDerivation, which, coq
  , metacoq, version ? null }:

with lib; mkCoqDerivation {
  pname = "elm-extraction";
  repo = "coq-elm-extraction";
  owner = "AU-COBRA";
  domain = "github.com";

  inherit version;

  defaultVersion = "dev";
  release."dev".rev       = "c538de01c2626aceca6d009c88ee4dba83602a98";
  release."dev".sha256    = "sha256-nshOhzwt4u4Wi1X59ztTmprpjqdvfEKhJx0zpkO6C9I=";

  propagatedBuildInputs = [ coq.ocamlPackages.findlib metacoq ];

  patchPhase = ''patchShebangs ./tests/process-extraction-examples.sh'';

  meta = {
    description = "A framework for extracting Coq programs to Elm";
    license = licenses.mit;
  };
}

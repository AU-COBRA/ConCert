{ lib, mkCoqDerivation, which, coq
  , metacoq, bignums, QuickChick, stdpp, rust-extraction, elm-extraction
  , version ? null }:

with lib; mkCoqDerivation {
  pname = "ConCert";
  repo = "ConCert";
  owner = "AU-COBRA";
  domain = "github.com";

  inherit version;
  ## The `defaultVersion` attribute is important for nixpkgs but can be kept unchanged
  ## for local usage since it will be ignored locally if
  ## - this derivation corresponds to the main attribute,
  ## - or its version is overridden (by a branch, PR, url or path) in `.nix/config.nix`.
  defaultVersion = with versions; switch coq.coq-version [
    ## Example of possible dependencies
    # { case = range "8.13" "8.14"; out = "1.2.0"; }
    ## other predicates are `isLe v`, `isLt v`, `isGe v`, `isGt v`, `isEq v` etc
  ] null;

  ## Declare existing releases
  ## leave sha256 empty at first and then copy paste
  ## the resulting sha given by the error message
  # release."1.1.1".sha256 = "";
  ## if the tag is not exactly the version number you can amend like this
  # release."1.1.1".rev = "v1.1.1";
  ## if a consistent scheme gives the tag from the release number, you can do like this:
  # releaseRev = v: "v${v}";

  propagatedBuildInputs = [ coq.ocamlPackages.findlib metacoq bignums QuickChick stdpp rust-extraction elm-extraction ];

  patchPhase = ''patchShebangs ./extraction/process-extraction-examples.sh'';

  meta = {
    description = "A framework for smart contract verification in Coq";
    ## Kindly ask one of these people if they want to be an official maintainer.
    ## (You might also consider adding yourself to the list of maintainers)
    # maintainers = with maintainers; [ cohencyril siraben vbgl Zimmi48 ];
    license = licenses.mit;
  };
}

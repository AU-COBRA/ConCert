{ lib, mkCoqDerivation, coq, ssreflect, coq-ext-lib, simple-io, version ? null }:

let recent = lib.versions.isGe "8.7" coq.coq-version; in
(mkCoqDerivation {
  pname = "QuickChick";
  owner = "4ever2";
  inherit version;
  defaultVersion = with lib; with versions; lib.switch [ coq.coq-version ssreflect.version ] [
      { cases = [ (range "8.15" "8.19") pred.true  ]; out = "2.0.2"; }
    ] null;
  release."2.0.2".rev       = "242abb33a6be32cd46200f666be48da25cb361c0";
  release."2.0.2".sha256    = "3TJs7e06kBivy7ItrM36sVFKhfAJPCxGPPfezBKH9jg=";
  releaseRev = v: "v${v}";

  preConfigure = lib.optionalString recent
    "substituteInPlace Makefile --replace quickChickTool.byte quickChickTool.native";

  mlPlugin = true;
  nativeBuildInputs = lib.optional recent coq.ocamlPackages.ocamlbuild;
  propagatedBuildInputs = [ ssreflect ]
    ++ lib.optionals recent [ coq-ext-lib simple-io ];
  extraInstallFlags = [ "-f Makefile.coq" ];

  enableParallelBuilding = false;

  meta = with lib; {
    description = "Randomized property-based testing plugin for Coq; a clone of Haskell QuickCheck";
    maintainers = with maintainers; [ jwiegley ];
  };
}).overrideAttrs (o:
  let after_1_6 = lib.versions.isGe "1.6" o.version || o.version == "dev";
  in {
    nativeBuildInputs = o.nativeBuildInputs
    ++ lib.optional after_1_6 coq.ocamlPackages.cppo;
    propagatedBuildInputs = o.propagatedBuildInputs
    ++ lib.optionals after_1_6 (with coq.ocamlPackages; [ findlib zarith ]);
})

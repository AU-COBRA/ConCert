{
  ## DO NOT CHANGE THIS
  format = "1.0.0";
  ## unless you made an automated or manual update
  ## to another supported format.

  attribute = "ConCert";

  default-bundle = "8.20";

  bundles."8.20" = {
    coqPackages.coq.override.version = "8.20";
    coqPackages.metacoq.override.version = "1.3.4-8.20";
    coqPackages.stdpp.override.version = "1.11.0";
    coqPackages.QuickChick.override.version = "2.0.4";
    coqPackages.RustExtraction.override.version = "c5d9cbae417213fe25b42f08678f28507cc6b99e";
    coqPackages.ElmExtraction.override.version = "0.1.0";
  };

  cachix.coq = {};
  cachix.coq-community = {};
  cachix.metacoq = {};

  cachix.au-cobra.authToken = "CACHIX_AUTH_TOKEN";
}

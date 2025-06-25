{
  ## DO NOT CHANGE THIS
  format = "1.0.0";
  ## unless you made an automated or manual update
  ## to another supported format.

  attribute = "ConCert";

  default-bundle = "9.00";

  bundles."9.0" = {
    coqPackages.coq.override.version = "9.0";
    coqPackages.metacoq.override.version = "1.3.4-9.0";
    coqPackages.stdpp.override.version = "1.11.0";
    coqPackages.QuickChick.override.version = "2.1.0";
    coqPackages.RustExtraction.override.version = "0.1.1";
    coqPackages.ElmExtraction.override.version = "0.1.1";
  };

  cachix.coq = {};
  cachix.coq-community = {};
  cachix.metacoq = {};

  cachix.au-cobra.authToken = "CACHIX_AUTH_TOKEN";
}

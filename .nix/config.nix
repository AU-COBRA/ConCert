{
  ## DO NOT CHANGE THIS
  format = "1.0.0";

  attribute = "ConCert";

  no-rocq-yet = true;

  default-bundle = "9.0";

  bundles."9.0" = {
    coqPackages.coq.override.version = "9.0";
    coqPackages.metarocq.override.version = "1.4-9.0.1";
    coqPackages.stdpp.override.version = "1.12.0";
    coqPackages.QuickChick.override.version = "2.1.1";
    coqPackages.RustExtraction.override.version = "0.1.1";
    coqPackages.ElmExtraction.override.version = "0.1.1";
  };

  cachix.coq = {};
  cachix.coq-community = {};
  cachix.metarocq = {};

  cachix.au-cobra.authToken = "CACHIX_AUTH_TOKEN";
}

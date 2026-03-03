{
  ## DO NOT CHANGE THIS
  format = "1.0.0";

  attribute = "ConCert";

  no-rocq-yet = true;

  default-bundle = "9.1";

  bundles."9.1" = {
    coqPackages.coq.override.version = "9.1";
    coqPackages.metarocq.override.version = "1.4.1-9.1";
    coqPackages.stdpp.override.version = "1.12.0";
    coqPackages.QuickChick.override.version = "2.1.1";
    coqPackages.TypedExtraction.override.version = "0.2.0";
  };

  cachix.coq = {};
  cachix.coq-community = {};
  cachix.metarocq = {};

  cachix.au-cobra.authToken = "CACHIX_AUTH_TOKEN";
}

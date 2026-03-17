{
  ## DO NOT CHANGE THIS
  format = "1.0.0";

  attribute = "ConCert";

  no-rocq-yet = true;

  default-bundle = "9.1";

  bundles."9.1" = {
    coqPackages = {
      coq.override.version = "9.1";
      metarocq-erasure.override.version = "1.5.1-9.1";
      stdpp.override.version = "1.13.0";
      QuickChick.override.version = "2.1.1";
      TypedExtraction.override.version = "0.2.1";
    };
    rocqPackages = {
      rocq-core.override.version = "9.1";
    };

    push-branches = ["master"];
  };

  cachix.coq = {};
  cachix.coq-community = {};
  cachix.metarocq = {};

  cachix.au-cobra.authToken = "CACHIX_AUTH_TOKEN";
}

{
  ## DO NOT CHANGE THIS
  format = "1.0.0";
  ## unless you made an automated or manual update
  ## to another supported format.

  attribute = "ConCert";

  default-bundle = "8.19";

  bundles."8.19" = {
    coqPackages.coq.override.version = "8.19";
    coqPackages.metacoq.override.version = "coq-8.19";
    coqPackages.stdpp.override.version = "1.10.0";
    coqPackages.QuickChick.override.version = "2.0.4";
  };

  cachix.coq = {};
  cachix.coq-community = {};
  cachix.metacoq = {};

  cachix.au-cobra.authToken = "CACHIX_AUTH_TOKEN";
}

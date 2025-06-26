{
  ## DO NOT CHANGE THIS
  format = "1.0.0";
  ## unless you made an automated or manual update
  ## to another supported format.

  attribute = "ConCert";

  default-bundle = "9.0";

  bundles."9.0" = {
    coqPackages.coq.override.version = "9.0";
    coqPackages.metarocq.override.version = "1.4-9.0";
    coqPackages.stdpp.override.version = "1.11.0";
    coqPackages.QuickChick.override.version = "2.1.0";
    coqPackages.RustExtraction.override.version = "rocq"; # Needs new release
    coqPackages.ElmExtraction.override.version = "rocq"; # Needs new release
  };

  cachix.coq = {};
  cachix.coq-community = {};
  cachix.metarocq = {};

  cachix.au-cobra.authToken = "CACHIX_AUTH_TOKEN";
}

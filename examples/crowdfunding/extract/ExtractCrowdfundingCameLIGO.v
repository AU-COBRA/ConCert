(** * Extraction of various contracts to CameLIGO *)

From MetaRocq.Template Require Import All.
From ConCert.Examples.Crowdfunding Require Import CrowdfundingCameLIGO.
From ConCert.Extraction Require Import CameLIGOPretty.
From ConCert.Extraction Require Import CameLIGOExtract.
From Stdlib Require Import List.

Import Crowdfunding.



#[local]
Existing Instance PrintConfShortNames.PrintWithShortNames.

Time MetaRocq Run
      (CameLIGO_prepare_extraction [] TT_remap_crowdfunding (TT_rename ++ TT_rename_ctors_default) [] "cctx_instance" CF_MODULE).

Time Definition cameLIGO_crowdfunding := Eval vm_compute in cameLIGO_crowdfunding_prepared.

(** We redirect the extraction result for later processing and compiling with the CameLIGO compiler *)
Redirect "cameligo-extract/CrowdfundingCertifiedExtraction.mligo"
MetaRocq Run (tmMsg cameLIGO_crowdfunding).

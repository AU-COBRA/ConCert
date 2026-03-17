(** Extraction of Dexter 2 to CameLIGO *)

From MetaRocq.Template Require Import All.
From ConCert.Extraction Require Import CameLIGOPretty.
From ConCert.Extraction Require Import CameLIGOExtract.
From ConCert.Examples.Dexter2 Require Import Dexter2CommonExtract.
From ConCert.Examples.Dexter2 Require Import Dexter2CPMMExtractLIGO.

Import Dexter2Extraction.

Local Open Scope string_scope.



Time MetaRocq Run
  (CameLIGO_prepare_extraction TT_inlines_dexter2 TT_remap_all
    TT_rename_ctors_default extra_ignore "cctx_instance" LIGO_DEXTER2_MODULE).

Time Definition cameLIGO_dexter2 := Eval vm_compute in cameLIGO_dexter2_prepared.

(** We redirect the extraction result for later processing and compiling with the CameLIGO compiler *)
Redirect "cameligo-extract/dexter2CertifiedExtraction.mligo"
  MetaRocq Run (tmMsg cameLIGO_dexter2).

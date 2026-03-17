(** Extraction of Dexter 2 to CameLIGO *)

From MetaRocq.Template Require Import All.
From ConCert.Execution Require Import BlockchainBase.
From ConCert.Extraction Require Import CameLIGOPretty.
From ConCert.Extraction Require Import CameLIGOExtract.
From ConCert.Examples.Dexter2 Require Import Dexter2CommonExtract.
From ConCert.Examples.Dexter2 Require Import Dexter2FA12ExtractLIGO.

Import Dexter2LqtExtraction.

Local Open Scope string_scope.


Section Extract.
  Context `{ChainBase}.

  Time MetaRocq Run
    (CameLIGO_prepare_extraction TT_inlines_dexter2 TT_remap_all
      TT_rename_ctors_default extra_ignore "cctx_instance" LIGO_DEXTER2LQT_MODULE).

  Time Definition cameLIGO_dexter2lqt := Eval vm_compute in cameLIGO_dexter2lqt_prepared.

  (** We redirect the extraction result for later processing and compiling with the CameLIGO compiler *)
  Redirect "cameligo-extract/dexter2fa12.mligo"
    MetaRocq Run (tmMsg cameLIGO_dexter2lqt).

End Extract.

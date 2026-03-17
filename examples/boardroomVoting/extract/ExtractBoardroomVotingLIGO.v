(** * Extraction of the Boardroom voting contract CameLIGO *)

(** We provide a configuration required for the contract extraction:
    additional remappings, definitions to inline, etc. *)
From MetaRocq.Template Require Import All.
From ConCert.Extraction Require Import CameLIGOExtract.
From ConCert.Extraction Require Import CameLIGOPretty.
From ConCert.Examples.BoardroomVoting Require Import BoardroomVotingExtractionCameLIGO.



#[local]
Existing Instance PrintConfShortNames.PrintWithShortNames.

Time MetaRocq Run (CameLIGO_prepare_extraction to_inline TT_remap TT_rename [] "cctx_instance" BV_MODULE).

Time Definition cameLIGO_boardroomvoting := Eval vm_compute in cameligo_boardroomvoting_prepared.

Redirect "cameligo-extract/BoardroomVoting.mligo"
MetaRocq Run (tmMsg cameLIGO_boardroomvoting).

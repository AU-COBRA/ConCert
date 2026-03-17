(** * Extraction of an interpreter for a stack based DSL *)
From MetaRocq.Template Require Import All.
From ConCert.Extraction Require Import CameLIGOPretty.
From ConCert.Extraction Require Import CameLIGOExtract.
From ConCert.Examples.StackInterpreter Require Import StackInterpreterLIGOExtract.

Import CameLIGOInterp.



#[local]
Existing Instance PrintConfShortNames.PrintWithShortNames.

Time MetaRocq Run
  (CameLIGO_prepare_extraction [] TT_remap_ligo TT_rename_ctors_default [] "cctx_instance" LIGO_INTERP_MODULE).

Time Definition cameligo_interp := Eval vm_compute in cameligo_interp_prepared.

(** We redirect the extraction result for later processing and compiling with the CameLIGO compiler *)
Redirect "cameligo-extract/StackInterpreter.mligo"
  MetaRocq Run (tmMsg cameligo_interp).

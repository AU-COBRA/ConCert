From ConCert.Execution Require Blockchain.
From ConCert.Execution.Examples Require Counter.
From ConCert.Extraction Require Import Common.
From ConCert.Extraction Require Import ConcordiumExtract.
From ConCert.Extraction Require Import ResultMonad.
From ConCert.Extraction Require Import RustExtract.
From Coq Require Import Bool.
From Coq Require Import List.
From Coq Require Import String.
From Coq Require Import ZArith.
From MetaCoq.Template Require Import All.

Import MonadNotation.
Import Printing.

Open Scope string.

Definition COUNTER_MODULE : ConcordiumMod _ _ :=
  {| concmd_contract_name := "counter";
     concmd_init := @ConCert.Execution.Examples.Counter.counter_init;
     concmd_receive := @ConCert.Execution.Examples.Counter.counter_receive;
     concmd_extra := []; |}.

MetaCoq Run (concordium_extraction
               COUNTER_MODULE
               (ConcordiumRemap.build_remaps
                  (ConcordiumRemap.remap_arith ++ ConcordiumRemap.remap_blockchain_consts)
                  []
                  (ConcordiumRemap.remap_blockchain_inductives
                     ++ ConcordiumRemap.remap_std_types))
               (fun kn => eq_kername <%% bool_rec %%> kn
                          || eq_kername <%% bool_rect %%> kn)).

From ConCert.Examples.Counter Require Counter.
From ConCert.Extraction Require Import Common.
From ConCert.Extraction Require Import ConcordiumExtract.
From RustExtraction Require Import RustExtract.
From Stdlib Require Import Bool.
From MetaRocq.Template Require Import All.



Definition COUNTER_MODULE : ConcordiumMod _ _ :=
  {| concmd_contract_name := "counter"%bs;
     concmd_init := @ConCert.Examples.Counter.Counter.counter_init;
     concmd_receive := @ConCert.Examples.Counter.Counter.counter_receive;
     concmd_extra := []; |}.

(* NOTE: it is important to declare a printing config, otherwise MetaRocq evaluation tries to normalize a term with an unresolved instance and runs out of memory. *)
#[local]
Instance RustConfig : RustPrintConfig :=
    {| term_box_symbol := "()";
       type_box_symbol := "()";
       any_type_symbol := "()";
       print_full_names := false |}.

Redirect "concordium-extract/counter.rs"
MetaRocq Run (concordium_extraction
               COUNTER_MODULE
               (ConcordiumRemap.build_remaps
                  (ConcordiumRemap.remap_Z_arith ++ ConcordiumRemap.remap_blockchain_consts)
                  []
                  (ConcordiumRemap.remap_blockchain_inductives
                     ++ ConcordiumRemap.remap_std_types))
               (fun kn => eq_kername <%% bool_rec %%> kn
                          || eq_kername <%% bool_rect %%> kn)).

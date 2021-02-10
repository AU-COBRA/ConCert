From Coq Require Import String.
From Coq Require Import List.
From Coq Require Import ZArith.
From Coq Require Import Bool.

From ConCert.Extraction Require Import RustExtract.
From ConCert.Extraction Require Import Common.
From ConCert.Extraction Require Import ConcordiumExtract.
From ConCert.Extraction Require Import ResultMonad.

From ConCert.Extraction.Examples Require Import CounterRefinementTypes.
From ConCert.Extraction.Examples Require Import CounterCertifiedExtraction.
From MetaCoq.Template Require Import All.

Import MonadNotation.
Import Printing.

Module CR := CounterRefinementTypes.
Module CS := CounterCertifiedExtraction.Counter.

Open Scope string.

Instance RustCounterConfig : RustPrintConfig :=
  {| term_box_symbol := "()";
     type_box_symbol := "()";
     any_type_symbol := "()";
     print_full_names := false |}.

Definition remap_blockchain : list (kername * string) := Eval compute in
      [ remap <%% PreludeExt.SimpleCallCtx %%> "type SimpleCallCtx<'a> = ();" ].

Definition remap_address : remapped_inductive :=
  {| re_ind_name := "AccountAddress";
     re_ind_ctors := [];
     re_ind_match := None |}.

Definition attrs : ind_attr_map :=
  fun kn => if eq_kername <%% CR.msg %%> kn || eq_kername <%% CS.msg %%> kn  then ["#[derive(Debug,Serialize)]"]
         else ["#[derive(Debug, Copy, Clone)]"].

Definition COUNTER_MODULE : ConcordiumMod _ _ :=
  {| concmd_contract_name := "counter";
     concmd_init := CounterRefinementTypes.init;
     concmd_receive := CounterRefinementTypes.counter;
     concmd_wrap_init := init_wrapper;
     concmd_wrap_receive := receive_wrapper_no_calls |}.

Import Blockchain.

Open Scope list.

Definition types_remap :=
  ConcordiumRemap.remap_std_types
    ++ [ (<%% @ActionBody %%>,  ConcordiumRemap.remap_Z )
        ; (<%% nat %%>, remap_address) ].

MetaCoq Run (res <- rust_extraction COUNTER_MODULE
                           (ConcordiumRemap.build_remaps
                              (ConcordiumRemap.remap_arith ++ remap_blockchain)
                              [] types_remap)
                           attrs
                           (fun kn => eq_kername <%% bool_rec %%> kn
                                   || eq_kername <%% bool_rect %%> kn);;
            tmMsg res).


Definition SIMPLE_COUNTER_MODULE : ConcordiumMod _ _ :=
  {| concmd_contract_name := "counter";
     concmd_init := CounterCertifiedExtraction.Counter.init;
     concmd_receive := CounterCertifiedExtraction.Counter.counter;
     concmd_wrap_init := init_wrapper;
     concmd_wrap_receive := receive_wrapper_no_calls |}.

MetaCoq Run (res <- rust_extraction SIMPLE_COUNTER_MODULE
                           (ConcordiumRemap.build_remaps
                              (ConcordiumRemap.remap_arith ++ remap_blockchain)
                              [] types_remap)
                           attrs
                           (fun kn => eq_kername <%% bool_rec %%> kn
                                   || eq_kername <%% bool_rect %%> kn);;
            tmMsg res).

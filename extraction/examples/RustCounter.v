From Coq Require Import String.
From Coq Require Import List.
From Coq Require Import ZArith.
From Coq Require Import Bool.

From ConCert.Extraction Require Import RustExtract.
From ConCert.Extraction Require Import Common.
From ConCert.Extraction Require Import ConcordiumExtract.
From ConCert.Extraction Require Import ResultMonad.

From ConCert.Extraction.Examples Require Import CounterRefinementTypes.
From MetaCoq.Template Require Import All.

Import MonadNotation.

Module C := CounterRefinementTypes.

Open Scope string.

Instance RustCounterConfig : RustPrintConfig :=
  {| term_box_symbol := "()";
     type_box_symbol := "()";
     any_type_symbol := "()";
     print_full_names := false |}.

Definition remap_blockchain : list (kername * string) := Eval compute in
      [ remap <%% C.Transaction  %%> "type Transaction<'a> = ();"
      ; remap <%% C.Transaction_none %%> "fn ##name## (&'a self) -> Transaction<'a> { () }"
      ; remap <%% PreludeExt.SimpleCallCtx %%> "type SimpleCallCtx<'a> = ();"].

Definition attrs : ind_attr_map :=
  fun kn => if eq_kername <%% C.msg %%> kn then ["#[derive(Debug,Serialize)]"]
         else ["#[derive(Debug, Copy, Clone)]"].

Definition COUNTER_MODULE : ConcordiumMod _ _ :=
  {| concmd_contract_name := "counter";
     concmd_init := CounterRefinementTypes.init;
     concmd_receive := CounterRefinementTypes.counter |}.

(* Definition counter_result:= *)
(*   Eval vm_compute in extract COUNTER *)
(*                              (ConcordiumRemap.build_remaps *)
(*                                 (ConcordiumRemap.remap_arith ++ remap_blockchain) *)
(*                                 [] *)
(*                                 (ConcordiumRemap.remap_std_types)) *)
(*                              attrs *)
(*                              (fun kn => eq_kername <%% bool_rec %%> kn *)
(*                                      || eq_kername <%% bool_rect %%> kn). *)

(* Definition rust_counter := *)
(*   match counter_result with *)
(*   | Ok v => tmMsg v *)
(*   | Err e => tmFail e *)
(*   end. *)

(* MetaCoq Run rust_counter. *)

MetaCoq Run (res <- rust_extraction COUNTER_MODULE
                           (ConcordiumRemap.build_remaps
                              (ConcordiumRemap.remap_arith ++ remap_blockchain)
                              []
                              (ConcordiumRemap.remap_std_types))
                           attrs
                           (fun kn => eq_kername <%% bool_rec %%> kn
                                   || eq_kername <%% bool_rect %%> kn);;
            tmMsg res).

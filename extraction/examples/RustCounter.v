From Coq Require Import String.
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
      ; remap <%% C.Transaction_none %%> "fn ##name## (&'a self) -> Transaction<'a> { () }" ].

(* TODO: remap <%% nat %%> "AccountAddress" *)

Time MetaCoq Run
     (r <- tmQuoteRecTransp CounterRefinementTypes.counter false;;
      tmDefinition "COUNTER" r
     ).

MetaCoq Quote Recursively Definition blah := bool_rect.

Definition counter_result:=
  Eval vm_compute in extract COUNTER
                             (ConcordiumRemap.build_remaps
                                (ConcordiumRemap.remap_arith ++ remap_blockchain)
                                []
                                (ConcordiumRemap.remap_std_types))
                             (fun kn => eq_kername <%% bool_rec %%> kn
                                     || eq_kername <%% bool_rect %%> kn).

Definition rust_counter :=
  match counter_result with
  | Ok v => tmMsg v
  | Err e => tmFail e
  end.

MetaCoq Run rust_counter.

(** * Extraction of a counter contract with refinement types to Midlang *)

(** The contract uses refinement types to specify some functional correctness properties *)
From ConCert.Execution Require Import Blockchain.
From ConCert.Execution Require Import Serializable.
From ElmExtraction Require Import Common.
From ElmExtraction Require Import ElmExtract.
From ElmExtraction Require Import PrettyPrinterMonad.
From MetaCoq.Erasure.Typed Require Import Extraction.
From MetaCoq.Erasure.Typed Require Import ResultMonad.
From MetaCoq.Common Require Import Kernames.
From MetaCoq.Template Require Import All.
From Coq Require Import List.
From Coq Require Import Lia.
From Coq Require Import String.
From Coq Require Import ZArith.

Import MCMonadNotation.
Open Scope string.

#[local]
Instance MidlangBoxes : ElmPrintConfig :=
  {| term_box_symbol := "()";
     type_box_symbol := "()";
     any_type_symbol := "()";
     false_elim_def := "false_rec ()";
     print_full_names := false |}.

Definition midlang_translation_map :=
  [(<%% @current_slot %%>, "current_slot");
  (<%% @address_eqb %%>, "address_eq");
  (<%% @ctx_amount %%>, "amount");
  (<%% @ctx_from %%>, "from");
  (<%% @Chain %%>, "ConCertChain");
  (<%% @ContractCallContext %%>, "ConCertCallContext");
  (<%% @ConCert.Execution.Blockchain.ActionBody %%>, "ConCertAction");
  (<%% @ChainBase %%>, "ChainBaseWTF");
  (<%% @ctx_contract_address %%>, "contract_address")].

Definition midlang_translate (name : kername) : option string :=
  match find (fun '(key, _) => eq_kername key name) midlang_translation_map with
  | Some (_, val) => Some val
  | None => None
  end.

Module CounterRefinmentTypes.

  Open Scope Z.
  Definition storage := Z.

  Inductive msg := Inc (_ : Z) | Dec (_ : Z).

  Program Definition inc_counter (st : storage) (inc : {z : Z | 0 <? z}) :
    {new_st : storage | st <? new_st} :=
    st + proj1_sig inc.
  Next Obligation.
    unfold is_true in *.
    rewrite <- Zlt_is_lt_bool in *; lia.
  Qed.


  Program Definition dec_counter (st : storage) (dec : {z : Z | 0 <? z}) :
    {new_st : storage | new_st <? st} :=
    st - proj1_sig dec.
  Next Obligation.
    unfold is_true in *.
    rewrite <- Zlt_is_lt_bool in *; lia.
  Qed.

  Definition my_bool_dec := Eval compute in Bool.bool_dec.

  Inductive SimpleActionBody :=
  | Act_transfer : nat -> Z -> SimpleActionBody.

  Definition Transaction := list SimpleActionBody.
  Definition Transaction_none : Transaction := [].

  Definition counter (msg : msg) (st : storage)
    : option (Transaction * storage) :=
    match msg with
    | Inc i =>
      match (my_bool_dec (0 <? i) true) with
      | left h => Some (Transaction_none, proj1_sig (inc_counter st (exist i h)))
      | right _ => None
      end
    | Dec i =>
      match (my_bool_dec (0 <? i) true) with
      | left h => Some (Transaction_none, proj1_sig (dec_counter st (exist i h)))
      | right _ => None
      end
    end.
End CounterRefinmentTypes.

MetaCoq Run
        (p <- tmQuoteRecTransp (CounterRefinmentTypes.counter) false;;
        tmDefinition "counter_env"%bs p.1).

Definition counter_name := <%% CounterRefinmentTypes.counter %%>.


(** A translation table for various constants we want to rename *)

Definition TT : list (kername * string) := Eval compute in
  [   remap <%% Z.add %%> "add"
    ; remap <%% Z.sub %%> "sub"
    ; remap <%% Z.leb %%> "le"
    ; remap <%% Z.ltb %%> "lt"
    ; remap <%% Z %%> "Int"
    ; ((<%% Z %%>.1, "Z0"%bs),"0")
    ; remap <%% nat %%> "AccountAddress"
    ; remap <%% CounterRefinmentTypes.Transaction %%> "Transaction"
    ; remap <%% CounterRefinmentTypes.Transaction_none %%> "Transaction.none"
    ; remap <%% bool %%> "Bool" ].

Definition midlang_counter_translate (name : kername) : option string :=
  match find (fun '(key, _) => eq_kername key name) (TT ++ midlang_translation_map) with
  | Some (_, val) => Some val
  | None => None
  end.

Definition ignored_concert_types :=
  Eval compute in
        [<%% @ActionBody %%>;
         <%% @Address %%>;
         <%% @Amount %%>;
         <%% @ChainBase %%>;
         <%% @Chain %%>;
         <%% @ContractCallContext %%>;
         <%% @SerializedValue %%>].


Definition counter_extract :=
    Eval vm_compute in
    extract_template_env_within_coq
      counter_env
      (KernameSet.singleton counter_name)
      (fun kn => List.existsb (eq_kername kn)
                              (ignored_concert_types
                                 ++ map fst midlang_translation_map
                                 ++ map fst TT)).

Definition counter_result := Eval compute in
     (env <- counter_extract ;;
      '(_, lines) <- finish_print_lines (print_env env midlang_counter_translate);;
      ret lines).

Definition wrap_in_delimiters s :=
  concat Common.nl [""; "{-START-} "; s; "{-END-}"].

Definition midlang_prelude :=
   ["import Basics exposing (..)";
    "import Blockchain exposing (..)";
    "import Bool exposing (..)";
    "import Int exposing (..)";
    "import Maybe exposing (..)";
    "import Order exposing (..)";
    "import Transaction exposing (..)";
    "import Tuple exposing (..)"].

MetaCoq Run (match counter_result with
             | Ok s => tmMsg "Extraction of counter succeeded"%bs
             | Err err => tmFail (String.of_string err)
             end).

Definition midlang_counter :=
  match counter_result with
  | Ok s => monad_map tmMsg (map String.of_string (midlang_prelude ++ s))
  | Err s => tmFail (String.of_string s)
  end.

Redirect "../extraction/tests/extracted-code/midlang-extract/CounterRefTypesMidlang.midlang"
  MetaCoq Run midlang_counter.

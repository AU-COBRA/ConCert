(** * A simply-typed version of the blockchain execution environment  *)
(* We develop some blockchain infrastructure relevant for the contract execution. *)
Require Import String ZArith Basics.
From ConCert.Embedding Require Import Ast Notations Prelude PCUICTranslate TranslationUtils.
From ConCert.Embedding.Examples Require Import Utils.
Require Import List.

From MetaCoq.Template Require Import All.

Import MonadNotation.

Import ListNotations.
Import BaseTypes.
Open Scope list.

(** We create a simply-typed records and data types corresponding for
the actual definitions of [SmartContracts.Blockchain] which are parameterised with [BaseTypes] *)

Module AcornBlockchain.
  Definition Address := Nat.
  Definition Money := Int.

  MetaCoq Run
        ( mp_ <- tmCurrentModPath tt ;;
          let mp := (PCUICTranslate.string_of_modpath mp_ ++ "@")%string in
          mkNames mp
                  ["SimpleChain" ; "Build_chain";
                  "SimpleContractCallContext" ; "Build_ctx" ;
                  "SimpleActionBody"] "_coq").


  Definition SimpleChainAcorn : global_dec :=
    [\ record SimpleChain :=
       Build_chain { "Chain_height" : BaseTypes.Nat;
                     "Current_slot" : BaseTypes.Nat;
                     "Finalized_height" : BaseTypes.Nat;
                     "Account_balance" : Address -> Money } \].

  MetaCoq Unquote Inductive (global_to_tc SimpleChainAcorn).

  Notation "'cur_time' a" := [| {eConst (to_string_name <% Current_slot %>)} {a} |]
                               (in custom expr at level 0).


  Definition SimpleContractCallContextAcorn : global_dec :=
    [\ record SimpleContractCallContext :=
       Build_ctx {
           (* Address sending the funds *)
           "Ctx_from" : Address;
           (* Address of the contract being called *)
           "Ctx_contract_address" : Address;
           (* Amount of currency passed in call *)
           "Ctx_amount" : Money} \].

  MetaCoq Unquote Inductive (global_to_tc SimpleContractCallContextAcorn).

  Definition SimpleActionBodyAcorn : global_dec :=
    [\ data SimpleActionBody =
          "Act_transfer" [Address, Money,_] \].

  MetaCoq Unquote Inductive (global_to_tc SimpleActionBodyAcorn).

  Notation SActionBody := (to_string_name <% SimpleActionBody_coq %>).

End AcornBlockchain.

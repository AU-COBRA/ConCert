(** * A simply-typed version of the blockchain execution environment  *)
(* We develop some blockchain infrastructure relevant for the contract execution. *)
Require Import String ZArith Basics.
From ConCert Require Import Ast Notations Prelude PCUICTranslate.
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
  Definition Money := "Coq.Numbers.BinNums.Z".


  Definition SimpleChainAcorn : global_dec :=
    [\ record "SimpleChain" :=
       "Build_chain" { "Chain_height" : "nat";
         "Current_slot" : "nat";
         "Finalized_height" : "nat";
         "Account_balance" : Address -> Money } \].

  Notation "'cur_time' a" := [| {eConst "Current_slot"} {a} |]
                               (in custom expr at level 0).

  Make Inductive (global_to_tc SimpleChainAcorn).

  Definition SimpleContractCallContextAcorn : global_dec :=
    [\ record "SimpleContractCallContext" :=
       "Build_ctx" {
           (* Address sending the funds *)
           "Ctx_from" : Address;
           (* Address of the contract being called *)
           "Ctx_contract_address" : Address;
           (* Amount of currency passed in call *)
           "Ctx_amount" : Money} \].

  Make Inductive (global_to_tc SimpleContractCallContextAcorn).

  Definition SimpleActionBodyAcorn : global_dec :=
    [\ data "SimpleActionBody" =
          "Act_transfer" [Address, Money,_] \].

  Make Inductive (global_to_tc SimpleActionBodyAcorn).

  Notation SActionBody := "SimpleActionBody".

End AcornBlockchain.

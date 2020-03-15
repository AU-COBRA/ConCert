Require Import String ZArith Basics.
From ConCert Require Import Ast Notations Prelude PCUICTranslate.
Require Import List.

From MetaCoq.Template Require Import All.

Import MonadNotation.

Import ListNotations.
Import BaseTypes.
Open Scope list.


Module CounterBlockchain.
  Definition Address := Nat.
  Definition CounterValue :=  Nat.

  Definition CounterChainAcorn : global_dec :=
    [\ record "CounterChain" :=
       "Build_chain" { "Chain_height" : "nat";
         "Current_slot" : "nat";
         "Finalized_height" : "nat";
         "Counter_value" : Address -> CounterValue } \].

  Notation "'cur_time' a" := [| {eConst "Current_slot"} {a} |]
                               (in custom expr at level 0).

  Make Inductive (global_to_tc CounterChainAcorn).

  Definition CounterContractCallContextAcorn : global_dec :=
    [\ record "CounterContractCallContext" :=
       "Build_ctx" {
           (* Address sending the funds *)
           "Ctx_from" : Address;
           (* Address of the contract being called *)
           "Ctx_contract_address" : Address} \].

  Make Inductive (global_to_tc CounterContractCallContextAcorn).

  Definition CounterActionBodyAcorn : global_dec :=
    [\ data "CounterActionBody" =
          "Act_transfer" [Address, Nat,_] \].

  Make Inductive (global_to_tc CounterActionBodyAcorn).

  Notation CActionBody := "CounterActionBody".

End CounterBlockchain.

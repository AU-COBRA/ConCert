From ConCert Require Import Blockchain BAT.
From ConCert Require Import Serializable.
From ConCert Require Import Containers.
From ConCert.Execution.QCTests Require Import TestUtils.

From QuickChick Require Import QuickChick. Import QcNotation.
From ExtLib.Structures Require Import Monads.
Import MonadNotation. Open Scope monad_scope.
From Coq Require Import List ZArith. Import ListNotations.

Module Type BATGensInfo.
  Parameter contract_addr : Address.
  Parameter gAccount : Chain -> G Address.
End BATGensInfo.

Module BATGens (Info : BATGensInfo).
Import Info.
Arguments SerializedValue : clear implicits.
Arguments deserialize : clear implicits.
Arguments serialize : clear implicits.

Definition serializeMsg := @serialize BAT.Msg _.

(*
  Generate create token requests on the form (from_addr, value, create_tokens)
  Has chance to generate request from both existing and new accounts
*)
Definition gCreateTokens (state : BAT.State) : G (Address * Amount * Msg) :=
  let nr_accounts_in_state := FMap.size (balances state) in
  let weight_1 := nr_accounts_in_state in
  let randomize_mk_gen g :=
    freq [
      (weight_1, returnGen g) ;
      (0, from_addr <- arbitrary ;; returnGen (from_addr, choose (0,3), create_tokens))
    ] in
  sample <- sampleFMapOpt (balances state) ;;
  match sample with
  | Some (from_addr, _) => randomize_mk_gen (from_addr, choose(0,3), create_tokens)
  | None => from_addr <- arbitrary ;; returnGen (from_addr, choose(0,3), create_tokens)
  end.
  



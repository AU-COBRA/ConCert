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

Definition account_balance (env : Environment) (addr : Address) : Amount :=
  (account_balance (env_chain env)) addr.

(*
  Generate create token requests on the form (from_addr, value, create_tokens)
  Has chance to generate request from both existing and new accounts
*)
Definition gCreateTokens (env : Environment) (state : BAT.State) : G (Address * Amount * Msg) :=
  let nr_accounts_in_state := FMap.size (balances state) in
  let randomize_mk_gen g :=
    freq [
      (nr_accounts_in_state, returnGen g) ;
      (5, from_addr <- gAccount env ;; value <- (choose (0, (account_balance env from_addr)))%Z ;; returnGen (from_addr, value, create_tokens))
    ] in
  sample <- sampleFMapOpt (balances state) ;;
  match sample with
  | Some (from_addr, _) => value <- (choose (0, (account_balance env from_addr)))%Z;; randomize_mk_gen (from_addr, value, create_tokens)
  | None => from_addr <- gAccount env ;; value <- (choose (0, (account_balance env from_addr)))%Z ;; returnGen (from_addr, value, create_tokens)
  end.

Definition gRefund (state : BAT.State) : G (Address * Msg) :=
  sample <- sampleFMapOpt (balances state) ;;
  match sample with
  | Some (from_addr, _) => returnGen (from_addr, refund)
  | None => from_addr <- arbitrary ;; returnGen (from_addr, refund) (* This will never happen *)
  end.

Definition gFinalize (state : BAT.State) : G (Address * Msg) :=
  sample <- sampleFMapOpt (balances state) ;;
  match sample with
  | Some (from_addr, _) => returnGen (from_addr, finalize)
  | None => from_addr <- arbitrary ;; returnGen (from_addr, finalize) (* This will never happen *)
  end.

(* Main generator. *)
Definition gBATAction (env : Environment) : GOpt Action :=
  let call contract_addr caller_addr value msg :=
    returnGenSome {|
      act_from := caller_addr;
      act_body := act_call contract_addr value (serializeMsg msg)
    |} in
  state <- returnGen (get_contract_state BAT.State env contract_addr) ;;
  backtrack [
    (* create_tokens *)
    (2, '(caller, value, msg) <- gCreateTokens env state ;;
        call contract_addr caller value msg
    );
    (* refund *)
    (1, '(caller, msg) <- gRefund state ;;
        call contract_addr caller (0%Z) msg
    );
    (* finalize *)
    (1, '(caller, msg) <- gFinalize state ;;
        call contract_addr caller (0%Z) msg
    )
  ].

End BATGens.




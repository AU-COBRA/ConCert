(** * Piggy Bank Contract *)
(** Implementation of a piggy bank smart contract.
    The contract is based on the Concordium example.
    https://developer.concordium.software/en/mainnet/smart-contracts/tutorials/piggy-bank/writing.html#piggy-bank-writing
*)
From ConCert.Utils Require Import RecordUpdate.
From ConCert.Execution Require Import Blockchain.
From ConCert.Execution Require Import ContractCommon.
From ConCert.Execution Require Import Monad.
From ConCert.Execution Require Import ResultMonad.
From ConCert.Execution Require Import Serializable.
From Coq Require Import List. Import ListNotations.
From Coq Require Import ZArith_base.



(** * Types *)
Section PiggyBankTypes.
  Local Set Nonrecursive Elimination Schemes.
  Local Set Primitive Projections.
  Context `{BaseTypes : ChainBase}.

  Inductive PiggyState :=
  | Intact
  | Smashed.

  Inductive Msg :=
  | Insert
  | Smash.

  Record State :=
    build_state {
      balance : Amount;
      owner : Address;
      piggyState : PiggyState
    }.

  Definition Setup : Type := unit.
  Definition Error : Type := N.
  Definition Result : Type := result (State * list ActionBody) Error.

  (* begin hide *)
  MetaCoq Run (make_setters State).

  Section Serialization.
    Global Instance piggyState_serializable : Serializable PiggyState :=
      Derive Serializable PiggyState_rect<Intact, Smashed>.

    Global Instance state_serializable : Serializable State :=
      Derive Serializable State_rect<build_state>.

    Global Instance msg_serializable : Serializable Msg :=
      Derive Serializable Msg_rect<Insert, Smash>.
  End Serialization.
  (* end hide *)
End PiggyBankTypes.

(** * Error codes *)
Section PiggyBankErrors.
  Open Scope N_scope.

  Definition error_no_msg : Error := 1.
  Definition error_not_owner : Error := 2.
  Definition error_already_smashed : Error := 3.
  Definition error_amount_not_positive : Error := 4.
  Definition error_amount_not_zero : Error := 5.
End PiggyBankErrors.

(** * Implementation *)
Section PiggyBankImpl.
  Context `{BaseTypes : ChainBase}.
  Open Scope Z.

  Definition is_smashed (state : State) : bool :=
    match state.(piggyState) with
    | Intact => false
    | Smashed => true
    end.

  Definition insert (state : State) (ctx : ContractCallContext) : Result :=
    let amount := ctx.(ctx_amount) in
    do _ <- throwIf (amount <? 0) error_amount_not_positive;
    do _ <- throwIf (is_smashed state) error_already_smashed;
    let state := state<| balance ::= Z.add amount |> in
    Ok (state, []).

  Definition smash (state : State) (ctx : ContractCallContext) : Result :=
    let owner := state.(owner) in
    do _ <- throwIf (address_neqb ctx.(ctx_from) owner) error_not_owner;
    do _ <- throwIf (is_smashed state) error_already_smashed;
    let acts := [act_transfer owner (state.(balance) + ctx.(ctx_amount))] in
    let state := state<| balance := 0 |><| piggyState := Smashed |> in
    Ok (state, acts).

  Definition receive (chain : Chain)
                     (ctx : ContractCallContext)
                     (state : State)
                     (msg : option Msg)
                     : Result :=
    match msg with
    | Some Insert => insert state ctx
    | Some Smash => smash state ctx
    | None => Err error_no_msg
    end.

  Definition init (chain : Chain)
                  (ctx : ContractCallContext)
                  (_ : Setup)
                  : result State Error :=
    Ok {|
      balance := ctx.(ctx_amount);
      owner := ctx.(ctx_from);
      piggyState := Intact
    |}.

  Definition contract : Contract Setup Msg State Error :=
    build_contract init receive.

End PiggyBankImpl.

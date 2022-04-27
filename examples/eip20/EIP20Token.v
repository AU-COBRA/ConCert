(** * EIP20 Token Implementation *)
(**
  This file contains an implementation of the EIP 20 Token Specification (https://eips.ethereum.org/EIPS/eip-20).
  
  The implementation is essentially a port of
  https://github.com/ConsenSys/Tokens/blob/fdf687c69d998266a95f15216b1955a4965a0a6d/contracts/eip20/EIP20.sol
*)
From Coq Require Import ZArith_base.
From Coq Require Import List. Import ListNotations.
From ConCert.Execution Require Import Monads.
From ConCert.Execution Require Import Serializable.
From ConCert.Execution Require Import Blockchain.
From ConCert.Execution Require Import Containers.
From ConCert.Execution Require Import ContractCommon.
From ConCert.Utils Require Import Extras.
From ConCert.Utils Require Import RecordUpdate.



(** * Contract types *)
Section EIP20Token.
  Context {BaseTypes : ChainBase}.
  Set Nonrecursive Elimination Schemes.

  Definition TokenValue := N.
  Open Scope N_scope.
  Open Scope bool.

  Inductive Msg :=
  | transfer : Address -> TokenValue -> Msg
  | transfer_from : Address -> Address -> TokenValue -> Msg
  | approve : Address -> TokenValue -> Msg.

  Record State :=
    build_state {
        total_supply : TokenValue;
        balances : AddressMap.AddrMap TokenValue;
        allowances : AddressMap.AddrMap (AddressMap.AddrMap TokenValue)
    }.

  Record Setup :=
    build_setup {
      owner : Address;
      init_amount : TokenValue;
    }.

  (* begin hide *)
  MetaCoq Run (make_setters State).
  MetaCoq Run (make_setters Setup).

  Section Serialization.

    Global Instance setup_serializable : Serializable Setup :=
      Derive Serializable Setup_rect <build_setup>.

    Global Instance msg_serializable : Serializable Msg :=
      Derive Serializable Msg_rect <transfer, transfer_from, approve>.

    Global Instance state_serializable : Serializable State :=
      Derive Serializable State_rect <build_state>.

  End Serialization.
  (* end hide *)

(** * Contract functions *)
  (** ** init *)
  (** Initialize contract storage *)
  Definition init (chain : Chain)
       (ctx : ContractCallContext)
       (setup : Setup) : option State :=
    Some {| total_supply := setup.(init_amount);
            balances := AddressMap.add setup.(owner) setup.(init_amount) AddressMap.empty;
            allowances := AddressMap.empty |}.

  Definition increment_balance (m : AddressMap.AddrMap TokenValue) (addr : Address) (inc : TokenValue) : AddressMap.AddrMap TokenValue :=
    match AddressMap.find addr m with
    | Some old => AddressMap.add addr (old + inc) m
    | None => AddressMap.add addr inc m
    end.

  (** ** transfer *)
  (** Transfers [amount] tokens, if [from] has enough tokens to transfer *)
  Definition try_transfer (from : Address)
       (to : Address)
       (amount : TokenValue)
       (state : State) : option State :=
    let from_balance := with_default 0 (AddressMap.find from state.(balances)) in
    if from_balance <? amount
    then None
    else let new_balances := AddressMap.add from (from_balance - amount) state.(balances) in
         let new_balances := increment_balance new_balances to amount in
         Some (state<|balances := new_balances|>).
  
  (** ** transfer_from *)
  (** The delegate tries to transfer [amount] tokens from [from] to [to].
      Succeeds if [from] has indeed allowed the delegate to spend at least [amount] tokens on its behalf. *)
  Definition try_transfer_from (delegate : Address)
       (from : Address)
       (to : Address)
       (amount : TokenValue)
       (state : State) : option State :=
  do from_allowances_map <- AddressMap.find from state.(allowances) ;
  do delegate_allowance <- AddressMap.find delegate from_allowances_map ;
  let from_balance := with_default 0 (AddressMap.find from state.(balances)) in
  if (delegate_allowance <? amount) || (from_balance <? amount)
  then None
  else let new_allowances := AddressMap.add delegate (delegate_allowance - amount) from_allowances_map in
       let new_balances := AddressMap.add from (from_balance - amount) state.(balances) in
       let new_balances := increment_balance new_balances to amount in
       Some (state<|balances := new_balances|><|allowances ::= AddressMap.add from new_allowances|>).

  (** ** approve *)
  (** The caller approves the delegate to transfer up to [amount] tokens on behalf of the caller *)
  Definition try_approve (caller : Address)
       (delegate : Address)
       (amount : TokenValue)
       (state : State) : option State :=
    match AddressMap.find caller state.(allowances) with
    | Some caller_allowances =>
      Some (state<|allowances ::= AddressMap.add caller (AddressMap.add delegate amount caller_allowances) |>)
    | None =>
      Some (state<|allowances ::= AddressMap.add caller (AddressMap.add delegate amount AddressMap.empty) |>)
    end.

  (** ** receive *)
  (** Contract entrypoint function *)
  Open Scope Z_scope.
  Definition receive (chain : Chain)
       (ctx : ContractCallContext)
       (state : State)
       (maybe_msg : option Msg)
    : option (State * list ActionBody) :=
    let sender := ctx.(ctx_from) in
    let without_actions := option_map (fun new_state => (new_state, [])) in
    (** Only allow calls with no money attached *)
    if ctx.(ctx_amount) >? 0
    then None
    else match maybe_msg with
   | Some (transfer to amount) => without_actions (try_transfer sender to amount state)
   | Some (transfer_from from to amount) => without_actions (try_transfer_from sender from to amount state)
   | Some (approve delegate amount) => without_actions (try_approve sender delegate amount state)
   (** transfer actions to this contract are not allowed *)
   | None => None
   end.
  Close Scope Z_scope.

  Definition contract : Contract Setup Msg State :=
    build_contract init receive.

  (* sum of all balances in the token state *)
  Definition sum_balances (state : EIP20Token.State) :=
    sumN (fun '(k, v) => v) (FMap.elements (balances state)).

  Definition get_allowance state from delegate :=
    with_default 0 (FMap.find delegate (with_default
      (@FMap.empty (FMap Address TokenValue) _) (FMap.find from (allowances state)))).

End EIP20Token.

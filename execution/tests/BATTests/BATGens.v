From ConCert Require Import Blockchain BAT.
From ConCert Require Import Serializable.
From ConCert Require Import Containers.
From ConCert.Execution.QCTests Require Import 
  TestUtils EIP20TokenGens.

From QuickChick Require Import QuickChick. Import QcNotation.
From ExtLib.Structures Require Import Monads.
Import MonadNotation. Open Scope monad_scope.
From Coq Require Import List ZArith. Import ListNotations.

Module Type BATGensInfo.
  Parameter contract_addr : Address.
  Parameter gAccount : Chain -> G Address.
  Parameter bat_addr : Address.
  Parameter fund_addr : Address.
End BATGensInfo.

Module BATGens (Info : BATGensInfo).
Import Info.
Arguments SerializedValue : clear implicits.
Arguments deserialize : clear implicits.
Arguments serialize : clear implicits.

Definition serializeMsg := @serialize BAT.Msg _.

Definition account_balance (env : Environment) (addr : Address) : Amount :=
  (env_account_balances env) addr.

Definition get_refundable_accounts state : list (G (option Address)) :=
  let balances_list := FMap.elements (balances state) in
  let filtered_balances := filter (fun x => (negb (address_eqb bat_addr (fst x))) && (0 <? (snd x))%N) balances_list in
    map returnGen (map Some (map fst filtered_balances)).

(*
  Generate create token requests on the form (from_addr, value, create_tokens)
  Has chance to generate request from both existing and new accounts
*)
Definition gCreateTokens (env : Environment) (state : BAT.State) : GOpt (Address * Amount * Msg) :=
  let current_slot := current_slot (env_chain env) in
  if (state.(isFinalized)
          || (Nat.ltb current_slot state.(fundingStart))
          || (Nat.ltb state.(fundingEnd) current_slot))
  then
    returnGen None
  else
      from_addr <- gAccount env ;;
      if (0 <? (account_balance env from_addr))%Z
      then
        value <- (choose (1, (account_balance env from_addr)))%Z ;; 
        returnGenSome (from_addr, value, create_tokens)
      else
        returnGen None.

Definition gRefund (env : Environment) (state : BAT.State) : GOpt (Address * Msg) :=
  let current_slot := current_slot (env_chain env) in
  let accounts := get_refundable_accounts state in
  if ((state.(isFinalized)
          || (Nat.leb current_slot state.(fundingEnd))
          || (state.(tokenCreationMin) <=? (total_supply state))%N)
)
  then
    returnGen None
  else 
    from_addr <- oneOf_ (returnGen None) accounts ;;
    returnGenSome (from_addr, refund).

Definition gFinalize (env : Environment) (state : BAT.State) : GOpt (Address * Msg) :=
  let current_slot := current_slot (env_chain env) in
  if (state.(isFinalized) 
        || ((total_supply state) <? state.(tokenCreationMin))%N
        || ((Nat.leb current_slot state.(fundingEnd)) && negb ((total_supply state) =? state.(tokenCreationCap))%N))
  then
    returnGen None
  else
    returnGenSome (fund_addr, finalize).

Module EIP20 := EIP20Gens Info.

(* Main generator. *)
Definition gBATAction (env : Environment) : GOpt Action :=
  let call contract_addr caller_addr value msg :=
    returnGenSome {|
      act_from := caller_addr;
      act_body := act_call contract_addr value (serializeMsg msg)
    |} in
  state <- returnGen (get_contract_state BAT.State env contract_addr) ;;
  backtrack [
    (* transfer *)
    (2, '(caller, msg) <- EIP20.gTransfer env (token_state state) ;;
        call contract_addr caller (0%Z) (tokenMsg msg)
    ) ;
    (* transfer_from *)
    (3, bindGenOpt (EIP20.gTransfer_from (token_state state))
        (fun '(caller, msg) =>
          call contract_addr caller (0%Z) (tokenMsg msg)
        )
    );
    (* approve *)
    (2, bindGenOpt (EIP20.gApprove (token_state state))
        (fun '(caller, msg) =>
          call contract_addr caller (0%Z) (tokenMsg msg)
        )
    );
    (* create_tokens *)
    (5, bindGenOpt (gCreateTokens env state)
        (fun '(caller, value, msg) =>
          call contract_addr caller value msg
        )
    );
    (* refund *)
    (10, bindGenOpt (gRefund env state)
        (fun '(caller, msg) =>
          call contract_addr caller (0%Z) msg
        )
    );
    (* finalize *)
    (10, bindGenOpt (gFinalize env state)
        (fun '(caller, msg) =>
          call contract_addr caller (0%Z) msg
        )
    )
  ].

End BATGens.




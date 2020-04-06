From Coq Require Import ZArith.
From Coq Require Import Morphisms.
Require Import Monads.
Require Import Extras.
Require Import Containers.
Require Import Automation.
From RecordUpdate Require Import RecordUpdate.
From Coq Require Import List.
Require Import Serializable.
Require Import Blockchain.
Import ListNotations.
Import RecordSetNotations.
From Coq Require Import Program.Basics.
Notation "f 'o' g" := (compose f g) (at level 50).

Require Import FA2Interface. 

Section FA2Token.
Context {BaseTypes : ChainBase}.
Set Primitive Projections.
Set Nonrecursive Elimination Schemes.
Open Scope N_scope.

Inductive FA2ReceiverMsg {Msg' : Type} `{Serializable Msg'} :=
  | receive_balance_of_param : list balance_of_response -> FA2ReceiverMsg
  | receive_total_supply_param : list total_supply_response -> FA2ReceiverMsg
  | receive_metadata_callback : list token_metadata -> FA2ReceiverMsg
  | receive_is_operator : is_operator_response  -> FA2ReceiverMsg
  | receive_permissions_descriptor : permissions_descriptor -> FA2ReceiverMsg
  | other_msg : Msg' -> FA2ReceiverMsg.

Inductive FA2TransferHook {Msg : Type} `{Serializable Msg} :=
  | transfer_hook : transfer_descriptor_param -> FA2TransferHook
  | hook_other_msg : Msg -> FA2TransferHook.

Inductive Msg := 
  | msg_transfer : list transfer -> Msg
  | msg_set_transfer_hook : set_hook_param -> Msg
  | msg_receive_hook_transfer : transfer_descriptor_param -> Msg
  | msg_balance_of : balance_of_param -> Msg
  | msg_total_supply : total_supply_param -> Msg
  | msg_token_metadata : token_metadata_param -> Msg
  | msg_permissions_descriptor : callback permissions_descriptor -> Msg (* TODO fix callback type *)
  | msg_update_operators : list update_operator -> Msg
  | msg_is_operator : is_operator_param -> Msg.

Record TokenLedger := 
  build_token_ledger {
    fungible : bool;
    balances : FMap Address N
}.

Record State :=
  build_state {
    fa2_owner          : Address;
    assets             : FMap token_id TokenLedger; 
    operators          : FMap Address (FMap Address operator_tokens);
    permission_policy  : permissions_descriptor;
    tokens             : FMap token_id token_metadata;
    transfer_hook_addr : option Address;
  }.

Record Setup :=
  build_setup {
    setup_total_supply        : list (token_id * N); (* is this necessary? *)
    setup_tokens              : FMap token_id token_metadata;
    initial_permission_policy : permissions_descriptor;
  }.

Instance token_ledger_settable : Settable _ :=
  settable! build_token_ledger <fungible; balances>.
Instance state_settable : Settable _ :=
  settable! build_state <fa2_owner; assets; operators; permission_policy; tokens; transfer_hook_addr>.
Instance setup_settable : Settable _ :=
  settable! build_setup <setup_total_supply; setup_tokens; initial_permission_policy>.

Section Serialization.

Global Instance setup_serializable : Serializable Setup :=
  Derive Serializable Setup_rect <build_setup>.

Global Instance FA2ReceiverMsg_serializable {Msg : Type} `{serMsg : Serializable Msg} : Serializable (@FA2ReceiverMsg Msg serMsg) :=
  Derive Serializable (@FA2ReceiverMsg_rect Msg serMsg) <
    (@receive_balance_of_param Msg serMsg), 
    (@receive_total_supply_param Msg serMsg), 
    (@receive_metadata_callback Msg serMsg), 
    (@receive_is_operator Msg serMsg), 
    (@receive_permissions_descriptor Msg serMsg), 
    (@other_msg Msg serMsg)>.

Global Instance FA2TransferHook_serializable {Msg : Type} `{serMsg : Serializable Msg} : Serializable (@FA2TransferHook Msg serMsg) :=
  Derive Serializable (@FA2TransferHook_rect Msg serMsg) <
    (@transfer_hook  Msg serMsg), 
    (@hook_other_msg Msg serMsg)>.  

Global Instance callback_permissions_descriptor_serializable : Serializable (callback permissions_descriptor) := callback_serializable.

Global Instance msg_serializable : Serializable Msg :=
  Derive Serializable Msg_rect <msg_transfer, msg_set_transfer_hook, msg_receive_hook_transfer, msg_balance_of, msg_total_supply, msg_token_metadata, msg_permissions_descriptor, msg_update_operators, msg_is_operator>.

Global Instance TokenLedger_serializable : Serializable TokenLedger :=
  Derive Serializable TokenLedger_rect <build_token_ledger>.

Global Instance state_serializable : Serializable State :=
	Derive Serializable State_rect <build_state>.
	
End Serialization.

Definition returnIf (cond : bool) := if cond then None else Some tt.

Definition address_balance (token_id : token_id)
                           (addr : Address)
                           (state : State) : N := 
  match FMap.find token_id state.(assets) with
  | Some ledger => with_default 0%N (FMap.find addr ledger.(balances))
  | None => 0%N
  end.

Definition address_has_sufficient_asset_balance (token_id : token_id) 
                                                (owner : Address) 
                                                (transaction_amount : N) 
                                                (state : State) 
                                                : option unit :=
  
  if transaction_amount <=? address_balance token_id owner state
  then Some tt
  else None. 

Definition policy_disallows_operator_transfer (policy : permissions_descriptor) : bool := 
  match policy.(descr_operator) with
  | operator_transfer_permitted => false 
  | operator_transfer_denied => true
  end.

Definition policy_disallows_self_transfer (policy : permissions_descriptor) : bool := 
  match policy.(descr_self) with
  | self_transfer_permitted => false 
  | self_transfer_denied => true
  end .

Definition get_owner_operator_tokens (owner operator : Address) 
                                     (state : State)
                                     : option operator_tokens := 
  do operator_tokens <- FMap.find owner state.(operators) ;
  FMap.find operator operator_tokens.

Definition try_single_transfer (caller : Address)
                               (params : transfer)
                               (state : State)
                               : option State :=
  do ledger <- FMap.find params.(transfer_token_id) state.(assets) ;
  let current_owner_balance := address_balance params.(transfer_token_id) params.(from_) state in
  let new_balances := FMap.add params.(from_) (current_owner_balance - params.(amount)) ledger.(balances) in
  let new_balances := FMap.partial_alter (fun balance => Some ((with_default 0 balance) + params.(amount))) params.(to_) new_balances in
  let new_ledger := ledger<|balances := new_balances|> in
  Some (state<|assets ::= FMap.add params.(transfer_token_id) new_ledger|>).

Definition transfer_check_permissions (caller : Address)
                                      (params : transfer)
                                      (policy : permissions_descriptor)
                                      (state : State)
                                      : option unit := 
  (* check for sufficient permissions *)
  do _ <- address_has_sufficient_asset_balance params.(transfer_token_id) params.(from_) params.(amount) state ;
  (* only allow transfers of known token_ids *)
  do _ <- FMap.find params.(transfer_token_id) state.(tokens) ;  
  (* if caller is owner of transfer, then check policy if self_transfer is allowed *)
  if (address_eqb caller params.(from_))
  then 
    returnIf (policy_disallows_self_transfer policy)
  else 
    (* check if policy allows operator transfer *)
    do _ <- returnIf (policy_disallows_operator_transfer policy) ;
    do operators_map <- FMap.find params.(from_) state.(operators) ;
    do op_tokens <- FMap.find caller operators_map ;
    (* check if operator has permission to transfer the given token_id type *)
    match op_tokens with
    | all_tokens => Some tt
    | some_tokens token_ids => if (existsb (fun id => id =? params.(transfer_token_id)) token_ids)
                               then Some tt
                               else None
    end.

Definition try_transfer (caller : Address)
                        (transfers : list transfer)
                        (state : State)
                        : option State :=
  let check_transfer_iterator state_opt params :=
    do state <- state_opt ;
    do _ <- transfer_check_permissions caller params state.(permission_policy) state;
    try_single_transfer caller params state in   
  (* returns the new state if all transfers *can* succeed, otherwise returns None *)
  fold_left check_transfer_iterator transfers (Some state).

(* Forwards the transfer to the hook to approve/reject *)
Definition call_transfer_hook (caller : Address)
                              (caddr : Address)
                              (transfer_hook_addr : Address)
                              (transfers : list transfer)
                              (state : State)
                              : ActionBody :=
  let mk_transfer_descr tr := {|
    transfer_descr_from_ := (tr.(from_));
    transfer_descr_to_ := (tr.(to_));
    transfer_descr_token_id := tr.(transfer_token_id);
    transfer_descr_amount := tr.(amount);
    |} in
  let transfer_decr_param := {|
    transfer_descr_fa2 := caddr;
    transfer_descr_batch := map mk_transfer_descr transfers;
    transfer_descr_operator := caller;
    |} in
  act_call transfer_hook_addr 0%Z (serialize (transfer_hook transfer_decr_param)).

(* Handles incoming transfers:
   - if the contract has a transfer_hook, then it uses the hook
   - otherwise it checks & performs the transfers now *)
Definition handle_transfer (caller : Address)
                           (caddr : Address)
                           (transfers : list transfer)
                           (state : State)
                           : option (State * list ActionBody) :=
  match state.(transfer_hook_addr) with
  (* send call transfer hook (approved transfers will be received in the msg_receive_hook_transfer endpoint) *)
  | Some transfer_hook_addr => 
    let call_hook_act := call_transfer_hook caller caddr transfer_hook_addr transfers state in 
    Some (state, [call_hook_act])
  (* perform transfers locally, now *)
  | None => option_map (fun new_state => (new_state, [])) (try_transfer caller transfers state)
  end.

Definition handle_transfer_hook_receive (caller : Address)
                                        (param : transfer_descriptor_param)
                                        (state : State)
                                        : option State :=
  (* check if caller is current hook - only hook is allowed to call this endpoint *)
  do hook_addr <- state.(transfer_hook_addr);
  do _ <- returnIf (negb (address_eqb caller hook_addr)) ;
  let mk_transfer_from_decr descr := 
    {|
      from_ := descr.(transfer_descr_from_);
      to_ := descr.(transfer_descr_to_);
      transfer_token_id := descr.(transfer_descr_token_id);
      amount := descr.(transfer_descr_amount);     
    |} in
  let transfers := map mk_transfer_from_decr param.(transfer_descr_batch) in
  try_transfer param.(transfer_descr_operator) transfers state.

Definition get_balance_of_callback (caller : Address)
                                     (param : balance_of_param)
                                     (state : State)
                                     : ActionBody :=
  let bal_req_iterator (bal_req : balance_of_request) :=
    let owner_bal := address_balance bal_req.(bal_req_token_id) bal_req.(owner) state in 
    Build_balance_of_response bal_req owner_bal in
  let responses := map bal_req_iterator param.(bal_requests) in
  let response_msg := serialize (receive_balance_of_param responses) in
  act_call caller 0%Z response_msg .

Definition get_total_supply_callback (caller : Address)
                                     (param : total_supply_param)
                                     (state : State)
                                     : ActionBody :=
  let token_id_balance (token_id : token_id) : N :=
    match FMap.find token_id state.(assets) with
    | Some ledger => fold_left N.add (FMap.values ledger.(balances)) 0%N
    | None => 0%N
    end in
  let mk_response (token_id : token_id) : total_supply_response := Build_total_supply_response token_id (token_id_balance token_id) in 
  let responses := map mk_response param.(supply_param_token_ids) in
  let response_msg := serialize (receive_total_supply_param responses) in
  act_call caller 0%Z response_msg.
  

Definition update_operators (caller : Address)
                            (updates : list update_operator)
                            (state : State)
                            : option State := 
  (* If policy doesn't allow operator transfer, then this operation fails *)
  do _ <- returnIf (policy_disallows_operator_transfer state.(permission_policy)) ;
  let exec_add params (state_opt : option State) : option State :=
    do state_ <- state_opt ;
    (* only the owner of the token is allowed to update their operators *)
    if (negb (address_eqb caller params.(op_param_owner)))
    then None
    else 
      let operator_tokens : FMap Address operator_tokens := with_default FMap.empty (FMap.find caller state_.(operators)) in
      (* Add new operator *)
      let operator_tokens := FMap.add params.(op_param_operator) params.(op_param_tokens) operator_tokens in
      Some (state_<| operators ::= FMap.add caller operator_tokens |>) in
  let exec_update state_ op := match op with
                               | add_operator params => exec_add params state_
                               | remove_operator params => exec_add params state_
                               end in 
  (fold_left exec_update updates (Some state)).

Definition operator_tokens_eqb (a b : operator_tokens) : bool := 
  match (a, b) with
  | (all_tokens, all_tokens) => true
  | (some_tokens a', some_tokens b') => 
    let fix my_list_eqb l1 l2 :=
      match (l1, l2) with
      | (x :: l1, y :: l2) => if x =? y
                              then my_list_eqb l1 l2
                              else false 
      | ([], []) => true
      | _ => false
      end in my_list_eqb a' b'
  | _ => false
  end.

Definition get_is_operator_response_callback (caller : Address)
                                             (params : is_operator_param)
                                             (state : State)
                                             : option (State * list ActionBody) :=
  (* if policy doesn't allow operator transfers, then this operation will fail *)
  do _ <- returnIf (policy_disallows_operator_transfer state.(permission_policy)) ;
  let operator_params := params.(is_operator_operator) in
  let operator_tokens_opt := get_owner_operator_tokens operator_params.(op_param_owner) operator_params.(op_param_operator) in
  let is_operator_result := match operator_tokens_opt state with
                            (* check if operator_tokens from the params and from the state are equal *)
                            | Some op_tokens => operator_tokens_eqb op_tokens operator_params.(op_param_tokens)
                            | None => false
                            end in
  let response : is_operator_response := {| operator := operator_params; is_operator := is_operator_result |} in
  let act := act_call caller 0%Z (serialize (receive_is_operator response)) in
  Some (state, [act]).

Definition get_permissions_descriptor_callback (caller : Address) (state : State) : ActionBody := 
  let response := serialize (receive_permissions_descriptor state.(permission_policy)) in
  act_call caller 0%Z response.

Definition try_set_transfer_hook (caller : Address)
                                 (params : set_hook_param)
                                 (state : State)
                                 : option State :=
  (* only owner can set transfer hook *)
  do _ <- returnIf (negb (address_eqb caller state.(fa2_owner))) ;
  Some (state<| transfer_hook_addr :=  Some params.(hook_addr)|>
             <| permission_policy  := params.(hook_permissions_descriptor) |>).


Definition get_token_metadata_callback (caller : Address) 
                                       (token_ids : list token_id) 
                                       (state : State)
                                       : ActionBody :=
  let state_tokens := state.(tokens) in
  let metadata_list : list token_metadata := fold_right (fun id acc => 
      match FMap.find id state_tokens with
      | Some metadata => metadata :: acc
      | None => acc
      end
    ) [] token_ids in
  let response := serialize (receive_metadata_callback metadata_list) in
  act_call caller 0%Z response.

Open Scope Z_scope.
Definition receive (chain : Chain)
						 			 (ctx : ContractCallContext)
									 (state : State)
									 (maybe_msg : option Msg)
					         : option (State * list ActionBody) :=
  let sender := ctx.(ctx_from) in
  let caddr := ctx.(ctx_contract_address) in
	let without_actions := option_map (fun new_state => (new_state, [])) in
	let without_statechange acts := Some (state, acts) in
	(* Only allow calls to this contract with no payload *)
	if ctx.(ctx_amount) >? 0
	then None
  else match maybe_msg with
  | Some (msg_transfer transfers) => handle_transfer sender caddr transfers state 
  | Some (msg_receive_hook_transfer param) => without_actions (handle_transfer_hook_receive sender param state)
  | Some (msg_is_operator params) => get_is_operator_response_callback sender params state 
  | Some (msg_balance_of params) => without_statechange [get_balance_of_callback sender params state]
  | Some (msg_total_supply params) => without_statechange [get_total_supply_callback sender params state]
  | Some (msg_permissions_descriptor _) => without_statechange [get_permissions_descriptor_callback sender state]
  | Some (msg_token_metadata param) => without_statechange [get_token_metadata_callback sender param.(metadata_token_ids) state]
  | Some (msg_update_operators updates) => without_actions (update_operators sender updates state)
  | Some (msg_set_transfer_hook params) => without_actions (try_set_transfer_hook sender params state)
  | _ => None
  end.  

Definition init (chain : Chain)
								(ctx : ContractCallContext)
								(setup : Setup) : option State := 
  Some {| permission_policy := setup.(initial_permission_policy);
          fa2_owner := ctx.(ctx_from);
          transfer_hook_addr := None;
          assets := FMap.empty;
          operators := FMap.empty;
          tokens := setup.(setup_tokens) |}.

Ltac solve_contract_proper :=
  repeat
    match goal with
    | [|- ?x _  = ?x _] => unfold x
    | [|- ?x _ _ = ?x _ _] => unfold x
    | [|- ?x _ _ _ = ?x _ _ _] => unfold x
    | [|- ?x _ _ _ _ = ?x _ _ _ _] => unfold x
    | [|- ?x _ _ _ _ = ?x _ _ _ _] => unfold x
    | [|- ?x _ _ _ _ _ = ?x _ _ _ _ _] => unfold x
    | [|- Some _ = Some _] => f_equal
    | [|- pair _ _ = pair _ _] => f_equal
    | [|- (if ?x then _ else _) = (if ?x then _ else _)] => destruct x
    | [|- match ?x with | _ => _ end = match ?x with | _ => _ end ] => destruct x
    | [H: ChainEquiv _ _ |- _] => rewrite H in *
    | _ => subst; auto
    end.

Lemma init_proper :
  Proper (ChainEquiv ==> eq ==> eq ==> eq) init.
Proof. repeat intro; solve_contract_proper.	Qed.

Lemma receive_proper :
  Proper (ChainEquiv ==> eq ==> eq ==> eq ==> eq) receive.
Proof. repeat intro; solve_contract_proper. Qed.

Definition contract : Contract Setup Msg State :=
  build_contract init init_proper receive receive_proper.

End FA2Token.
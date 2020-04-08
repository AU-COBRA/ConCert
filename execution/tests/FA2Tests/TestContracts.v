From ConCert Require Import Blockchain LocalBlockchain FA2Token FA2Interface.
From ConCert Require Import Serializable.
From Coq Require Import Morphisms.

Require Import Monads.
Require Import Extras.
Require Import Containers.
Require Import Automation.
From RecordUpdate Require Import RecordUpdate.
From Coq Require Import List.
Require Import ZArith.
Import ListNotations.
Import RecordSetNotations.

Section FA2Client.
Context {BaseTypes : ChainBase}.
Set Primitive Projections.
Set Nonrecursive Elimination Schemes.
Open Scope N_scope.

Inductive FA2ClientMsg :=
  | Call_fa2_is_operator : is_operator_param -> FA2ClientMsg 
  | Call_fa2_balance_of_param : list balance_of_response -> FA2ClientMsg
  | Call_fa2_total_supply_param : list total_supply_response -> FA2ClientMsg
  | Call_fa2_metadata_callback : list token_metadata -> FA2ClientMsg
  | Call_fa2_permissions_descriptor : permissions_descriptor -> FA2ClientMsg.

Global Instance FA2ClientMsg_serializable : Serializable FA2ClientMsg :=
  Derive Serializable FA2ClientMsg_rect <
    Call_fa2_is_operator, 
    Call_fa2_balance_of_param, 
    Call_fa2_total_supply_param,
    Call_fa2_metadata_callback,
    Call_fa2_permissions_descriptor>.

Definition ClientMsg := @FA2ReceiverMsg BaseTypes FA2ClientMsg _.

Record ClientState := 
  build_clientstate {
  fa2_caddr : Address;
  bit : N;
}.

Record ClientSetup := 
  build_clientsetup {
  fa2_caddr_ : Address
}.

Instance state_settable : Settable _ :=
  settable! build_clientstate <fa2_caddr; bit>.
Instance setup_settable : Settable _ :=
  settable! build_clientsetup <fa2_caddr_>.

Section Serialization.

Global Instance setup_serializable : Serializable ClientSetup :=
  Derive Serializable ClientSetup_rect <build_clientsetup>.

Global Instance state_serializable : Serializable ClientState :=
	Derive Serializable ClientState_rect <build_clientstate>.

Global Instance ClientMsg_serializable : Serializable ClientMsg := FA2Token.FA2ReceiverMsg_serializable.

End Serialization.
  
Definition client_init (chain : Chain)
								(ctx : ContractCallContext)
								(setup : ClientSetup) : option ClientState := 
  Some {|
    fa2_caddr := setup.(fa2_caddr_);
    bit := 0;
	|}.

Definition client_receive (chain : Chain)
						 			 (ctx : ContractCallContext)
									 (state : ClientState)
									 (maybe_msg : option ClientMsg)
									 : option (ClientState * list ActionBody) :=
	match maybe_msg with
  | Some (receive_is_operator is_op_response) => Some (state<| bit:= 42|>, [])
  | Some (other_msg (Call_fa2_is_operator is_op_param)) => 
      Some (state<| bit := 2|>, [act_call state.(fa2_caddr) 0%Z (@serialize FA2Token.Msg _ (FA2Token.msg_is_operator is_op_param))])
  | _ => None 
	end.

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

Lemma client_init_proper :
  Proper (ChainEquiv ==> eq ==> eq ==> eq) client_init.
Proof. repeat intro; solve_contract_proper.	Qed.

Lemma client_receive_proper :
  Proper (ChainEquiv ==> eq ==> eq ==> eq ==> eq) client_receive.
Proof. repeat intro; solve_contract_proper. Qed.

Definition client_contract : Contract FA2Client.ClientSetup ClientMsg FA2Client.ClientState :=
  build_contract client_init client_init_proper client_receive client_receive_proper.

End FA2Client.

(* A contract which implements the transfer hook endpoint of FA2 *)
(* Behavior is driven by a permission policy *)

Section FA2TransferHook.
Context {BaseTypes : ChainBase}.
Set Primitive Projections.
Set Nonrecursive Elimination Schemes.
Open Scope N_scope.

Inductive FA2TransferHookMsg :=
  | set_permission_policy : permissions_descriptor -> FA2TransferHookMsg.

Global Instance FA2TransferHookMsg_serializable : Serializable FA2TransferHookMsg :=
  Derive Serializable FA2TransferHookMsg_rect <
    set_permission_policy>.

Definition TransferHookMsg := @FA2TransferHook BaseTypes FA2TransferHookMsg _.

Record HookState := 
  build_hookstate {
    hook_owner : Address;
    hook_fa2_caddr : Address;
    hook_policy : permissions_descriptor;
}.

Record HookSetup := 
  build_hooksetup {
    hook_fa2_caddr_ : Address;
    hook_policy_ : permissions_descriptor;
}.

Instance hookstate_settable : Settable _ :=
  settable! build_hookstate <hook_owner; hook_fa2_caddr; hook_policy>.
Instance hooksetup_settable : Settable _ :=
  settable! build_hooksetup <hook_fa2_caddr_; hook_policy_>.

Section Serialization.

Global Instance hooksetup_serializable : Serializable HookSetup :=
  Derive Serializable HookSetup_rect <build_hooksetup>.

Global Instance hookstate_serializable : Serializable HookState :=
	Derive Serializable HookState_rect <build_hookstate>.

End Serialization.
  
Definition hook_init (chain : Chain)
								(ctx : ContractCallContext)
								(setup : HookSetup) : option HookState := 
  Some {|
    hook_owner := ctx.(ctx_from);
    hook_fa2_caddr := setup.(hook_fa2_caddr_);
    hook_policy := setup.(hook_policy_);
	|}.

Definition returnIf (cond : bool) := if cond then None else Some tt.

Definition check_transfer_permissions (tr : transfer_descriptor)
                                      (operator : Address)
                                      (state : HookState) 
                                      : option unit :=
  if (address_eqb tr.(transfer_descr_from_) operator)
  then if (FA2Token.policy_disallows_self_transfer state.(hook_policy))
    then None 
    else Some tt
  else if (FA2Token.policy_disallows_operator_transfer state.(hook_policy))
    then None
    else Some tt.

(* called whenever this hook receives a transfer from the FA2 contract *)
(* checks the permission policy, and if all transfers are valid, 
   forwards the transfers to the 'msg_receive_hook_transfer' endpoint of the FA2 Contract *)
Definition on_hook_receive_transfer (caller : Address)
                                    (param : transfer_descriptor_param)
                                    (state : HookState)
                                    : option (list ActionBody) :=
  do _ <- returnIf (negb (address_eqb caller state.(hook_fa2_caddr))) ;
  do _ <- returnIf (negb (address_eqb param.(transfer_descr_fa2) state.(hook_fa2_caddr))) ;
  let operator := param.(transfer_descr_operator) in
  let check_transfer_iterator tr acc :=
    do _ <- check_transfer_permissions tr operator state ;
    Some tt in
  (* check if all transfers satisfy the permission policy. If at least one does not, the whole operation fails *)
  do _ <- fold_right check_transfer_iterator (Some tt) param.(transfer_descr_batch) ;
  (* send out transfer action *)
  let msg := @serialize FA2Token.Msg _ (msg_receive_hook_transfer param) in
  Some [(act_call caller 0%Z msg)].

Definition try_update_permission_policy (caller : Address)
                                    (new_policy : permissions_descriptor)
                                    (state : HookState)
                                    : (option HookState) :=
  do _ <- returnIf (negb (address_eqb caller state.(hook_owner))) ;
  Some (state<| hook_policy := new_policy |>).

Definition hook_receive (chain : Chain)
						 			 (ctx : ContractCallContext)
									 (state : HookState)
									 (maybe_msg : option TransferHookMsg)
                   : option (HookState * list ActionBody) :=
  let sender := ctx.(ctx_from) in
  let without_actions := option_map (fun new_state => (new_state, [])) in
	let without_statechange := option_map (fun acts => (state, acts)) in
  match maybe_msg with
  | Some (transfer_hook param) => without_statechange (on_hook_receive_transfer sender param state)
  | Some (hook_other_msg (set_permission_policy policy)) => without_actions (try_update_permission_policy sender policy state)
  | _ => None 
	end.

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

Lemma hook_init_proper :
  Proper (ChainEquiv ==> eq ==> eq ==> eq) hook_init.
Proof. repeat intro; solve_contract_proper.	Qed.

Lemma hook_receive_proper :
  Proper (ChainEquiv ==> eq ==> eq ==> eq ==> eq) hook_receive.
Proof. repeat intro; solve_contract_proper. Qed.

Definition hook_contract : Contract HookSetup TransferHookMsg HookState :=
  build_contract hook_init hook_init_proper hook_receive hook_receive_proper.

End FA2TransferHook.
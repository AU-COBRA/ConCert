(*
  A buggy version of the EIP20/ERC20 token implementation where transfer_from incorrectly updates balances whenever sender=receiver.
  This mimics the vulnerability of iToken, as discovered in https://bzx.network/blog/incident
*)

From Coq Require Import ZArith.
From Coq Require Import Morphisms.
Require Import Monads.
Require Import Extras.
Require Import Containers.
Require Import Automation.
Require Import EIP20Token.
From RecordUpdate Require Import RecordUpdate.
From Coq Require Import List.
Require Import Serializable.
Require Import Blockchain.

Import ListNotations.
Import RecordSetNotations.

Section EIP20Token_Buggy.
  Context {BaseTypes : ChainBase}.
  Set Primitive Projections.
  Set Nonrecursive Elimination Schemes.

  Open Scope N_scope.
  Existing Instance state_settable.
  Existing Instance setup_settable.

  (* The delegate tries to transfer <amount> tokens from <from> to <to>.
   Succeeds if <from> has indeed allowed the delegate to spend at least <amount> tokens on its behalf. *)
  Local Open Scope bool_scope.
  Definition transfer_from_buggy (delegate : Address)
       (from : Address)
       (to : Address)
       (amount : TokenValue)
       (state : State) : option State :=
  do from_allowances_map <- FMap.find from state.(allowances) ;
  do delegate_allowance <- FMap.find delegate from_allowances_map ;
  let from_balance := with_default 0 (FMap.find from state.(balances)) in
  (* Bug starts here! to_balance is calculated too early! *)
  let to_balance := with_default 0 (FMap.find to state.(balances)) in
  if ((delegate_allowance <? amount) && negb (from =? to)%address) || (from_balance <? amount)
  then None
  else let new_allowances := FMap.add delegate (delegate_allowance - amount) from_allowances_map in
       let new_balances := FMap.add from (from_balance - amount) state.(balances) in
       (* Bug here! new balance of 'to' is calculated from to_balance. The commented line below is the correct implementation. *)
       let new_balances := FMap.add to (to_balance + amount) new_balances in
       (* let new_balances := FMap.partial_alter (fun balance => Some (with_default 0 balance + amount)) to new_balances in *)
       Some (state<|balances := new_balances|><|allowances ::= FMap.add from new_allowances|>).

  Definition init_buggy := EIP20Token.init. 

  Open Scope Z_scope.
  Definition receive_buggy (chain : Chain)
       (ctx : ContractCallContext)
       (state : State)
       (maybe_msg : option Msg)
    : option (State * list ActionBody) :=
    let sender := ctx.(ctx_from) in
    let without_actions := option_map (fun new_state => (new_state, [])) in
    (* Only allow calls with no money attached *)
    if ctx.(ctx_amount) >? 0
    then None
    else match maybe_msg with
   | Some (transfer_from from to amount) => without_actions (transfer_from_buggy sender from to amount state)
   | _ => EIP20Token.receive chain ctx state maybe_msg 
   end.
  Close Scope Z_scope.

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

  Lemma init_buggy_proper :
    Proper (ChainEquiv ==> eq ==> eq ==> eq) init_buggy.
  Proof. repeat intro; solve_contract_proper. Qed.

  Lemma receive_buggy_proper :
    Proper (ChainEquiv ==> eq ==> eq ==> eq ==> eq) receive_buggy.
  Proof. repeat intro; solve_contract_proper. Qed.

  Definition contract : Contract Setup Msg State :=
    build_contract init_buggy init_buggy_proper receive_buggy receive_buggy_proper.

End EIP20Token_Buggy.

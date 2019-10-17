(** * Contract examples  *)

(** We develop some blockchain infrastructure relevant for the contract execution (a fragment of the standard library and an execution context). With that, we develop a deep embedding of a crowdfunding contract and prove some of its properties using the corresponding shallow embedding *)

Require Import String Basics.
Require Import Ast Notations CustomTactics PCUICTranslate PCUICtoTemplate.
Require Import List.
Require Import PeanoNat.
Require Import Coq.ssr.ssrbool.

Import ListNotations.
From MetaCoq.Template Require Import All.

Import MonadNotation.
Import BaseTypes.
Import StdLib.
Open Scope list.

Definition expr_to_tc Σ := compose trans (expr_to_term Σ).
Definition type_to_tc := compose trans type_to_term.
Definition global_to_tc := compose trans_minductive_entry trans_global_dec.


(** Our approximation for finite maps. Eventually, will be replaced with the Oak's standard library implementation. We assume that the standard library is available for a contract developer. *)

Section Maps.
  Open Scope nat.

  Inductive addr_map : Set :=
  | mnil | mcons : nat -> nat -> addr_map -> addr_map.

  Inductive Maybe_map :=
  | Just_map : nat -> Maybe_map | Nothing_map.

  Definition Maybe := "Maybe_map".

  Fixpoint lookup_map (m : addr_map) (key : nat) : Maybe_map :=
    match m with
    | mnil => Nothing_map
    | mcons k v m' =>
      if (Nat.eqb key k) then Just_map v else lookup_map m' key
    end.

  (* Ported from FMapWeaklist of StdLib *)
  Fixpoint add_map (k : nat) (x : nat) (s : addr_map) : addr_map :=
  match s with
   | mnil => mcons k x mnil
   | mcons k' y l => if Nat.eqb k k' then mcons k x l else mcons k' y (add_map k x l)
  end.

  Definition inmap_map k m := match lookup_map m k with
                              | Just_map _ => true
                              | Nothing => false
                              end.

  Lemma lookup_map_add k v m : lookup_map (add_map k v m) k = Just_map v.
  Proof.
    induction m.
    + simpl. now rewrite PeanoNat.Nat.eqb_refl.
    + simpl. destruct (k =? n) eqn:Heq.
      * simpl. now rewrite PeanoNat.Nat.eqb_refl.
      * simpl. now rewrite Heq.
  Qed.

End Maps.

Notation "a ∈ m" := (inmap_map a m = true) (at level 50).
Notation "a ∉ m" := (inmap_map a m = false) (at level 50).

(** Generation of string constants using MetaCoq *)
Fixpoint mkNames (ns : list string) (postfix : string) :=
  match ns with
  | [] => tmPrint "Done."
  | n :: ns' => n' <- tmEval all (n ++ postfix)%string ;;
                  str <- tmQuote n';;
                  tmMkDefinition n str;;
                  mkNames ns' postfix
  end.

(** Notations for functions on finite maps *)

Definition Map := "addr_map".

Notation "'mfind' a b" :=  [| {eConst "lookup_map"} {a} {b} |]
        (in custom expr at level 0,
            a custom expr at level 1,
            b custom expr at level 1).

Notation "'madd' a b c" :=  [| {eConst "add_map"} {a} {b} {c} |]
        (in custom expr at level 0,
            a custom expr at level 1,
            b custom expr at level 1,
            c custom expr at level 1).

Notation "'mem' a b" :=  [| {eConst "inmap_map"} {a} {b} |]
        (in custom expr at level 0,
            a custom expr at level 1,
            b custom expr at level 1).

(** * Contract execution context  *)

(** The contract execution context is a part of the blockchain infrastructure, not specific to this particular example. We assume that these structures reflect the actual implementation.  *)

Record ctx := mkctx { _ctx_from : nat;
                      _ctx_contract_address : nat ;
                      _amount : nat;
                      _cur_time : nat}.

Definition ctx_from_name := "_ctx_from".
Definition Ctx := "ctx".
Notation "'ctx_from' a" := [| {eConst ctx_from_name} {a} |]
                             (in custom expr at level 0).
Notation "'ctx_contract_address' a" :=
  [| {eConst "_ctx_contract_address"} {a} |]
    (in custom expr at level 0).
Notation "'amount' a" := [| {eConst "_amount"} {a} |]
                             (in custom expr at level 0).
Notation "'cur_time' a" := [| {eConst "_cur_time"} {a} |]
                             (in custom expr at level 0).

(** ** The crowdfunding contract *)

Module CrowdfundingContract.

  (** Note that we define the deep embedding (abstract syntax trees) of the data structures and programs using notations. These notations are defined in  [Ast.v] and make use of the "custom entries" feature. The idea is that the corresponding ASTs will be produced from the real Oak programs by means of printing the fully annotated abstract syntax trees build from constructors of the inductive type [Ast.expr] *)

   (** Brackets like [[\ \]] delimit the scope of global definitions and like [[| |]] the scope of programs *)

  (** We model types of addresses and currency by [nat] type of Coq *)
  Notation Address := Nat.
  Definition Money := Nat.

  (** Generating names for the data structures  *)
  Run TemplateProgram
      (mkNames ["State" ; "mkState"; "balance" ; "donations" ; "owner"; "deadline"; "goal"; "done";
                "Result" ; "Res" ; "Error";
                "Msg"; "Donate"; "GetFunds"; "Claim";
                "Action"; "Transfer"; "Empty" ] "_coq").

  Import ListNotations.

  (** *** Definitions of data structures for the contract *)

  (** The internal state of the contract *)
  Definition state_syn : global_dec :=
    [\ record State :=
        mkState { balance : Money ;
                  donations : Map;
                  owner : Money;
                  deadline : Nat;
                  done : Bool;
                  goal : Money } \].

  (** We can print actual AST by switching off the notations *)

  Unset Printing Notations.

  Print state_syn.
  (* state_syn =
      gdInd State O
        (cons
           (rec_constr State
              (cons (pair (nNamed balance) (tyInd Money))
                 (cons (pair (nNamed donations) (tyInd Map))
                    (cons (pair (nNamed owner) (tyInd Money))
                       (cons (pair (nNamed deadline) (tyInd Nat))
                          (cons (pair (nNamed goal) (tyInd Money)) nil)))))) nil) true
           : global_dec *)

  Set Printing Notations.

  (** Unquoting the definition of a record *)
  Make Inductive (global_to_tc state_syn).

  (** As a result, we get a new Coq record [State_coq] *)
  Print State_coq.

  (** AST of action that our contract can produce *)
  Definition action_syn :=
    [\ data Action =
         Transfer [Address, Money, _]
         | Empty [_] \].

  Make Inductive (global_to_tc action_syn).

  (** AST for the type of results *)
  Definition result_syn :=
    [\ data Result =
         Res [State, Action, _]
       | Error [_] \].

  Make Inductive (global_to_tc result_syn).

  Definition msg_syn :=
    [\ data Msg =
         Donate [_]
       | GetFunds [_]
       | Claim  [_] \].

  Make Inductive (global_to_tc msg_syn).

  (** Custom notations for patterns, projections and constructors *)
  Module Notations.

    (** Patterns *)
    Notation "'Donate'" :=
      (pConstr Donate []) (in custom pat at level 0).
    Notation "'GetFunds'" :=
      (pConstr GetFunds []) ( in custom pat at level 0).

    Notation "'Claim'" :=
      (pConstr Claim []) ( in custom pat at level 0).

    Notation "'Just' x" :=
      (pConstr "Just" [x]) (in custom pat at level 0,
                               x constr at level 4).
    Notation "'Nothing'" := (pConstr "Nothing" [])
                              (in custom pat at level 0).

    (** Projections *)
    Notation "'balance' a" :=
      [| {eConst balance} {a} |]
        (in custom expr at level 0).
    Notation "'donations' a" :=
      [| {eConst donations} {a} |]
        (in custom expr at level 0).
    Notation "'owner' a" :=
      [| {eConst owner} {a} |]
        (in custom expr at level 0).
    Notation "'deadline' a" :=
      [| {eConst deadline} {a} |]
        (in custom expr at level 0).
    Notation "'goal' a" :=
      [| {eConst goal} {a} |]
        (in custom expr at level 0).
    Notation "'done' a" :=
      [| {eConst done} {a} |]
        (in custom expr at level 0).


    (** Constructors *)
    Notation "'Res' a b" :=
      [| {eConstr Result Res} {a} {b} |]
        (in custom expr at level 0,
            a custom expr at level 1,
            b custom expr at level 1).

    Notation "'Error'" := (eConstr Result Error)
                        (in custom expr at level 0).

    Notation "'mkState' a b" :=
      [| {eConstr State "mkState_coq"} {a} {b} |]
        (in custom expr at level 0,
            a custom expr at level 1,
            b custom expr at level 1).

    Notation "'Transfer' a b" :=
      [| {eConstr Action Transfer} {a} {b} |]
        (in custom expr at level 0,
            a custom expr at level 1,
            b custom expr at level 1).

    Notation "'Empty'" := (eConstr Action Empty)
                        (in custom expr at level 0).

    (** New global context with the constants defined above (in addition to the ones defined in the Oak's "StdLib") *)


    Definition Σ' :=
      Σ ++ [gdInd Ctx 0 [("ExampleContracts.mkctx",
                        [(None,tyInd Address); (None,tyInd Address)])] false;
              gdInd Maybe 0 [("Just", [(None,tyInd Nat)]);
                             ("Nothing", [])] false;
            state_syn;
            result_syn;
            msg_syn;
            action_syn].


    End Notations.

  Import Notations.


  (** Generating string constants for variable names *)

  Run TemplateProgram (mkNames ["c";"s";"e";"m";"v";
                                "tx_amount"; "bal"; "sender"; "own"; "isdone" ;
                                "accs"; "now";
                                 "newstate"; "newmap"; "cond"] "").
  (** A shortcut for [if .. then .. else ..]  *)
  Notation "'if' cond 'then' b1 'else' b2 : ty" :=
    (eCase (Bool,[]) (tyInd ty) cond
           [(pConstr true_name [],b1);(pConstr false_name [],b2)])
      (in custom expr at level 2,
          cond custom expr at level 4,
          ty constr at level 4,
          b1 custom expr at level 4,
          b2 custom expr at level 4).

  (** *** The AST of a crowdfunding contract *)
  Definition crowdfunding : expr :=
    [| \c : Ctx => \m : Msg => \s : State =>
         let bal : Money := balance s in
         let now : Nat := cur_time c in
         let tx_amount : Money := amount c in
         let sender : Address := ctx_from c in
         let own : Address := owner s in
         let accs : Map := donations s in
         case m : Msg return Result of
            | GetFunds ->
             if (own == sender) && (deadline s < now) && (goal s <= bal)  then
               Res (mkState 0 accs own (deadline s) True (goal s))
                   (Transfer bal sender)
             else Error : Result
           | Donate -> if now <= deadline s then
             (case (mfind accs sender) : Maybe return Result of
               | Just v ->
                 let newmap : Map := madd sender (v + tx_amount) accs in
                 Res (mkState (tx_amount + bal) newmap own (deadline s) (done s) (goal s)) Empty
               | Nothing ->
                 let newmap : Map := madd sender tx_amount accs in
                 Res (mkState (tx_amount + bal) newmap own (deadline s) (done s) (goal s)) Empty)
               else Error : Result
           | Claim ->
             if (deadline s < now) && (bal < goal s) && (~ done s) then
             (case (mfind accs sender) : Maybe return Result of
              | Just v -> let newmap : Map := madd sender 0 accs in
                  Res (mkState (bal-v) newmap own (deadline s) (done s) (goal s))
                      (Transfer v sender)
               | Nothing -> Error)
              else Error : Result
    |].

  Make Definition entry :=
    (expr_to_tc Σ' (indexify nil crowdfunding)).

  Ltac inv_andb H := apply Bool.andb_true_iff in H;destruct H.
  Ltac split_andb := apply Bool.andb_true_iff;split.


  Open Scope nat.
  Open Scope bool.

  Import Lia.

  Definition deadline_passed now (s : State_coq) := s.(deadline_coq) <? now.

  Definition goal_reached (s : State_coq) := s.(goal_coq) <=? s.(balance_coq).

  Definition funded now (s : State_coq) :=
    deadline_passed now s && goal_reached s.

  Lemma not_leb n m : ~~ (n <=? m) -> m <? n.
  Proof.
   intros.
   unfold Nat.ltb in *.
   unfold is_true in *. rewrite Bool.negb_true_iff in *.
   rewrite Nat.leb_gt in *. rewrite Nat.leb_le in *. lia.
  Qed.

  Lemma not_ltb n m : ~~ (n <? m) -> m <=? n.
  Proof.
   intros.
   unfold Nat.ltb in *.
   unfold is_true in *. rewrite Bool.negb_true_iff in *.
   rewrite Nat.leb_gt in *. rewrite Nat.leb_le in *. lia.
  Qed.

  (** ** Properties of the crowdfunding contract *)

  (** This function is a simplistic execution environment that performs one step of execution *)
  Definition run (entry : State_coq -> Result_coq ) (init : State_coq)
    : State_coq * Action_coq :=
    match entry init with
    | Res_coq fin out => (fin, out)
    | Error_coq => (init, Empty_coq) (* if an error occurs, the state remains the same *)
    end.

  (** A wrapper for the assertions about the contract execution *)
  Definition assertion (pre : State_coq -> Prop)
             (entry : State_coq -> Result_coq )
             (post : State_coq -> Action_coq -> Prop) :=
    forall init, pre init -> exists fin out, run entry init = (fin, out) /\ post fin out.

  Notation "{{ P }} c {{ Q }}" := (assertion P c Q)( at level 50).


  (** The donations can be paid back to the backers if the goal is not
reached within a deadline *)

  Lemma get_money_back_guarantee CallCtx (sender := CallCtx.(_ctx_from)) v :
      (* pre-condition *)
      {{ fun init =>
         deadline_passed CallCtx.(_cur_time) init
       /\ ~~ (goal_reached init)
       /\ ~~ init.(done_coq)
       /\ lookup_map init.(donations_coq) sender = Just_map v }}

        (* contract call *)
       entry CallCtx Claim_coq

       (* post-condition *)
       {{fun fin out => lookup_map fin.(donations_coq) sender = Just_map 0
         /\ out = Transfer_coq v sender}}.
  Proof.
    unfold assertion. intros init H. simpl.
    destruct H as [Hdl [Hgoal [Hndone Hlook]]].
    unfold deadline_passed,goal_reached in *;simpl in *.
    repeat eexists. unfold run. simpl.
    assert (balance_coq init <? goal_coq init = true) by now apply not_leb.
    repeat destruct (_ <? _);tryfalse.
    destruct (~~ done_coq _)%bool;tryfalse.
    destruct (lookup_map _ _);tryfalse;inversion Hlook;subst;clear Hlook.
    repeat split;cbn. apply lookup_map_add.
  Qed.

  (** New donations are recorded correctly in the contract's state *)

  Lemma new_donation_correct CallCtx (sender := CallCtx.(_ctx_from))
        (donation := CallCtx.(_amount)) :

    {{ fun init =>
          sender ∉ init.(donations_coq) (* the sender have not donated before *)
       /\ ~~ deadline_passed CallCtx.(_cur_time) init }}

      (* contract call *)
    entry CallCtx Donate_coq

    {{ fun fin out =>
         (* nothing gets transferred *)
         out = Empty_coq
         (* donation has been accepted *)
         /\ lookup_map fin.(donations_coq) sender = Just_map donation  }}.
  Proof.
    unfold assertion. intros init H. simpl.
    destruct H as [Hnew_sender Hdl].
    unfold deadline_passed in *;simpl in *.
    unfold run.
    repeat eexists.
    simpl in *. apply not_ltb in Hdl.
    destruct (_ <=? _);tryfalse.
    unfold inmap_map in *.
    destruct (lookup_map _ _);tryfalse.
    repeat split;eauto. simpl. now rewrite lookup_map_add.
  Qed.


  (** Existing donations are updated correctly in the contract's state *)

  Lemma existing_donation_correct CallCtx (sender := CallCtx.(_ctx_from))
        (new_don := CallCtx.(_amount)) old_don :
    {{ fun init =>
         (* the sender has already donated before *)
         lookup_map init.(donations_coq) sender = Just_map old_don

       /\ ~~ deadline_passed CallCtx.(_cur_time) init }}

     entry CallCtx Donate_coq

    {{ fun fin out =>
         (* nothing gets transferred *)
         out = Empty_coq
         (* donation has been added *)
       /\ lookup_map fin.(donations_coq) sender = Just_map (new_don + old_don) }}.
  Proof.
    unfold assertion. intros init H. simpl.
    destruct H as [Hsender Hdl].
    unfold deadline_passed in *;simpl in *.
    subst;simpl in *.
    eexists. eexists.
    unfold run. simpl in *. apply not_ltb in Hdl.
    destruct (_ <=? _);tryfalse.
    destruct (lookup_map _ _);tryfalse.
    inversion Hsender;subst.
    repeat split;simpl;eauto. now rewrite lookup_map_add.
  Qed.

  Fixpoint sum_map  (m : addr_map) :=
    match m with
    | mnil => 0
    | mcons _ v m' => v + sum_map m'
    end.

  Lemma sum_map_add_in m : forall n0 v' v k,
      lookup_map m k = Just_map n0 ->
      sum_map m = v ->
      sum_map (add_map k (n0+v') m) = v' + v.
  Proof.
    intros;subst.
    revert dependent n0. revert v' k.
    induction m;intros;subst.
    + inversion H.
    + simpl in *. destruct (k =? n) eqn:Hkn.
      * simpl in *. inversion H. subst. lia.
      * simpl in *. rewrite IHm;auto. lia.
  Qed.

  Lemma sum_map_add_not_in m : forall v' v k,
      lookup_map m k = Nothing_map ->
      sum_map m = v ->
      sum_map (add_map k v' m) = v' + v.
  Proof.
    intros;subst.
    revert dependent k. revert v'.
    induction m;intros;subst.
    + reflexivity.
    + simpl in *. destruct (k =? n) eqn:Hkn.
      * inversion H.
      * simpl in *. rewrite IHm;auto. lia.
  Qed.

  (** The contract does no leak funds: the overall balance before the deadline is always equal to the sum of individual donations *)

  Definition consistent_balance ctx state :=
    ~~ deadline_passed ctx.(_cur_time) state /\
    sum_map state.(donations_coq) = state.(balance_coq).

  (** This lemma holds for any message  *)
  Lemma contract_backed CallCtx msg :

    {{ consistent_balance CallCtx }}

      entry CallCtx msg

    {{ fun fin _ => consistent_balance CallCtx fin }}.
  Proof.
    intros init H.
    destruct H as [Hdl Hsum].
    destruct msg.
    + (* Donate *)
      simpl in *.
      specialize Hdl as Hdl'.
      unfold deadline_passed in Hdl. unfold run,consistent_balance.
      apply not_ltb in Hdl.  simpl.
      destruct (_ <=? _);tryfalse.
      destruct (lookup_map _ _) eqn:Hlook.
      * repeat eexists;eauto. now apply sum_map_add_in.
      * repeat eexists;eauto. now apply sum_map_add_not_in.
    + (* GetFunds - it is not possible to get funds before the deadline, so the state is not modified *)
      unfold consistent_balance in *.
      unfold deadline_passed in *.
      exists init. exists Empty_coq. unfold run. simpl.
      destruct (_ <? _);tryfalse. rewrite Bool.andb_false_r. simpl.
      split;eauto.
    + (* Claim - it is not possible to claim a donation back before the deadline, so the state is not modified *)
      unfold consistent_balance in *.
      unfold deadline_passed in *.
      exists init. exists Empty_coq. unfold run. simpl.
      destruct (_ <? _);tryfalse. simpl.
      split;eauto.
  Qed.

  (** The owner gets the money after the deadline, if the goal is reached *)

  Lemma GetFunds_correct CallCtx (OwnerAddr := CallCtx.(_ctx_from)) funds :
    {{ fun init => funded CallCtx.(_cur_time) init
       /\ init.(owner_coq) =? OwnerAddr
       /\ balance_coq init = funds }}

    entry CallCtx GetFunds_coq

    {{ fun fin out =>
       (* the money are sent back *)
       out = Transfer_coq funds OwnerAddr
       (* set balance to 0 after withdrawing by the owner *)
       /\  fin.(balance_coq) = 0
       (* set the "done" flag *)
       /\ fin.(done_coq) = true}}.
  Proof.
    unfold assertion. intros init H. simpl.
    destruct H as [Hfunded [Hown Hbalance]]. unfold funded,goal_reached,deadline_passed in *.
    subst. simpl in *.
    unfold run. simpl in *. subst OwnerAddr. eexists. eexists.
    destruct (_ <? _);tryfalse. destruct ( _ =? _);tryfalse. simpl in *.
    destruct (_ <=? _);tryfalse. split;eauto.
  Qed.

  (** Backers cannot claim their money if the campaign have succeed (but owner haven't claimed the money yet, so the "done" flag is not set to [true]) *)
  Lemma no_claim_if_succeeded CallCtx the_state:
    {{ fun init =>
         funded CallCtx.(_cur_time) init
         /\ ~~ init.(done_coq)
         /\ init = the_state }}

      entry CallCtx Claim_coq

    (* Nothing happens - the stated stays the same and no outgoing transfers *)
    {{ fun fin out => fin = the_state /\ out = Empty_coq }}.
  Proof.
    unfold assertion. intros init H. simpl.
    unfold funded,deadline_passed,goal_reached in *. subst. simpl in *.
    destruct H as [Hdl [Hgoal Hst]].
    inv_andb Hdl. subst. unfold run. simpl.
    exists the_state. eexists.
    destruct the_state as [i_balance i_dons i_own i_dl i_done i_goal].
    destruct CallCtx as [from c_addr am now]. simpl in *.

    destruct (_ <? _);tryfalse. destruct (_ <=? _) eqn:Hleb;tryfalse.
    replace (i_balance <? i_goal) with false by
        (symmetry;rewrite Nat.ltb_ge in *; rewrite Nat.leb_le in *;lia).
    now simpl.
  Qed.

  (** Backers cannot claim their money if the contract is marked as "done" *)
  Lemma no_claim_after_done CallCtx the_state :
    {{ fun init => init.(done_coq) /\ init = the_state }}

     entry CallCtx Claim_coq
    (* Nothing happens - the stated stays the same and no outgoing transfers *)
    {{ fun fin out => fin = the_state /\ out = Empty_coq }}.
  Proof.
    unfold assertion. intros init H. simpl. destruct H. subst.
    unfold funded,deadline_passed,goal_reached in *. subst. simpl in *.
    exists the_state. eexists.
    unfold run. simpl in *. destruct (done_coq _);tryfalse. simpl in *.
    now rewrite Bool.andb_false_r.
  Qed.
End CrowdfundingContract.

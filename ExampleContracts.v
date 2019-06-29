(** * Examples  *)
Require Import String.
Require Import Ast CustomTactics.
Require Import List.
Require Import PeanoNat.
Import ListNotations.
From Template Require Import All.

Import MonadNotation.
Import BaseTypes.
Import StdLib.
Open Scope list.

(** Our approximation for finite maps. Eventually, will be replaced with the Oak's standard library implementation. We assume that the standard library is available for a contarct developer. *)

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
  Function add_map (k : nat) (x : nat) (s : addr_map) : addr_map :=
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

Definition ctx_from_name := "ExampleContracts._ctx_from".
Definition Ctx := "ExampleContracts.ctx".
Notation "'ctx_from' a" := [| {eConst ctx_from_name} {a} |]
                             (in custom expr at level 0).
Notation "'ctx_contract_address' a" :=
  [| {eConst "ExampleContracts._ctx_contract_address"} {a} |]
    (in custom expr at level 0).
Notation "'amount' a" := [| {eConst "_amount"} {a} |]
                             (in custom expr at level 0).
Notation "'cur_time' a" := [| {eConst "_cur_time"} {a} |]
                             (in custom expr at level 0).

(** ** The crowdfunding contract *)

Module CrowdfundingContract.

  (** Note that we define the deep embedidng of the data structures an  programs (AST) using notations. These notations are defined in  [Ast.v] and make use of the "custom entries" feature. The idea is that the corresponding ASTs will be produced from the real Oak programs by means of printing the fully annotated syntax in terms of the constructors of the inductive type [Ast.expr] *)

  (** Brackets like [\ \] delimit the scope of global definitions and like [| |] the scope of programs *)

  (** We model types of addresses and currency by [nat] type of Coq *)
  Notation Address := Nat.
  Definition Money := Nat.

  (** Generating names for the data structures  *)
  Run TemplateProgram
      (mkNames ["State" ; "balance" ; "donations" ; "owner"; "deadline"; "goal";
                "Result" ; "Res" ; "Error";
                "Msg"; "Donate"; "GetFunds"; "Claim";
                "Action"; "Transfer"; "Empty" ] "_coq").

  Import ListNotations.

  (** *** Definitions of data structures for the contract *)

  (** The internal state of the contract *)
  Definition state_syn : global_dec :=
    [\ record State :=
       { balance : Money ;
         donations : Map;
         owner : Money;
         deadline : Nat;
         goal : Money } \].

  (** We can print actual AST by swithing off the notations *)

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
  Make Inductive (trans_global_dec state_syn).

  (** As a result, we get a new Coq record [State_coq] *)
  Print State_coq.

  (** AST of action that our contract can produce *)
  Definition action_syn :=
    [\ data Action :=
         Transfer : Address -> Money -> Action
    | Empty : Action; \].

  Make Inductive (trans_global_dec action_syn).

  (** AST for the type of results *)
  Definition result_syn :=
    [\ data Result :=
         Res : State -> Action -> Result
       | Error : Result; \].

  Make Inductive (trans_global_dec result_syn).

  Definition msg_syn :=
    [\ data Msg :=
       Donate : Msg
       | GetFunds : Msg
       | Claim : Msg; \].

  Make Inductive (trans_global_dec msg_syn).

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
                        [(nAnon,tyInd Address); (nAnon,tyInd Address)])] false;
              gdInd Maybe 0 [("Just", [(nAnon,tyInd Nat)]);
                             ("Nothing", [])] false;
            state_syn;
            result_syn;
            msg_syn;
            action_syn].


    End Notations.

  Import Notations.


  (** Generating string constants for varable names *)

  Run TemplateProgram (mkNames ["c";"s";"e";"m";"v";
                                "tx_amount"; "bal"; "sender"; "own";
                                "accs"; "now";
                                  "newstate"; "newmap"; "cond"] "").
  (** A shortcut for [if .. then .. else ..]  *)
  Notation "'if' cond 'then' b1 'else' b2 : ty" :=
    (eCase (tyInd Bool,0) (tyInd ty) cond
           [(pConstr true_name [],b1);(pConstr false_name [],b2)])
      (in custom expr at level 2,
          cond custom expr at level 4,
          ty constr at level 4,
          b1 custom expr at level 4,
          b2 custom expr at level 4).

  (** *** The AST of a crowdfunding contract *)
  Definition crowdfunding : expr :=
    [| \c : Ctx => \s : State =>  \m : Msg =>
         let bal : Money := balance s in
         let now : Nat := cur_time c in
         let tx_amount : Money := amount c in
         let sender : Address := ctx_from c in
         let own : Address := owner s in
         let accs : Map := donations s in
         case m : Msg return Result of
            | GetFunds ->
             if (own == sender) && (deadline s < now) && (goal s <= bal)  then
               Res (mkState 0 accs own (deadline s) (goal s)) (Transfer bal sender)
             else Error : Result
           | Donate -> if now <= deadline s then
             (case (mfind accs sender) : Maybe return Result of
               | Just v ->
                 let newmap : Map := madd sender (v + tx_amount) accs in
                 Res (mkState (tx_amount + bal) newmap own (deadline s) (goal s)) Empty
               | Nothing ->
                 let newmap : Map := madd sender tx_amount accs in
                 Res (mkState (tx_amount + bal) newmap own (deadline s) (goal s)) Empty)
               else Error : Result
           | Claim ->
             if (deadline s < now) && (bal < goal s) then
             (case (mfind accs sender) : Maybe return Result of
              | Just v -> let newmap : Map := madd sender 0 accs in
                  Res (mkState (bal-v) newmap own (deadline s) (goal s))
                      (Transfer v sender)
               | Nothing -> Error)
              else Error : Result
    |].

  Make Definition entry :=
    Eval compute in (expr_to_term Σ' (indexify nil crowdfunding)).

  Ltac inv_andb H := apply Bool.andb_true_iff in H;destruct H.
  Ltac split_andb := apply Bool.andb_true_iff;split.


  Open Scope nat.
  Open Scope bool.


  Definition deadline_passed now (s : State_coq) := s.(deadline_coq) <? now.

  Definition goal_reached (s : State_coq) := s.(goal_coq) <=? s.(balance_coq).

  Definition funded now (s : State_coq) :=
    deadline_passed now s && goal_reached s.

  (** ** Properties of the crowdfunding contract *)

  (** The donations can be paid back to the backers if the goal is not
reached within a deadline *)

  Lemma get_money_back_guarantee (init_state final_state: State_coq)
        CallCtx  msg sender out_tx v :
    (* pre-condition *)
    sender = CallCtx.(_ctx_from) -> msg = Claim_coq (* a sender claims the money*)
    -> funded CallCtx.(_cur_time) init_state = true
    -> lookup_map init_state.(donations_coq) sender = Just_map v (* the sender donated [v] *)

    -> entry CallCtx init_state msg = Res_coq final_state out_tx

    (* post-condition *)
    -> out_tx = Transfer_coq v sender (* the money are sent back *)
      /\ lookup_map final_state.(donations_coq) sender = Just_map 0. (* balance of the sender put to zero *)
  Proof.
    simpl.
    intros Hsender Hmsg Hfunded Hlook Hcall.
    subst;simpl in *.  inv_andb Hfunded.
    (* direct rewriting with [Hlook] or [Hgoal] cannot unify terms
       in Hcall for some reason, but destruct with underscores works *)
    destruct (_ && _)%bool;tryfalse.
    destruct (lookup_map _ _);tryfalse; inversion Hlook;subst;clear Hlook.
    split.
    * inversion Hcall. reflexivity.
    * inversion Hcall. subst. simpl.
      now rewrite lookup_map_add.
  Qed.


  (** New donations are recorded correctly in the contract's state *)

  Lemma new_donation_correct (init_state final_state: State_coq)
        CallCtx  msg sender out_tx donation :
    (* pre-condition *)
    sender = CallCtx.(_ctx_from) -> msg = Donate_coq
    -> CallCtx.(_amount) = donation  (* a sender donates [donation] *)
    -> sender ∉ init_state.(donations_coq) (* the sender have not donated before *)
    -> CallCtx.(_cur_time) <= init_state.(deadline_coq) (* deadline have not passed *)

    -> entry CallCtx init_state msg = Res_coq final_state out_tx

    (* post-condition *)
    -> out_tx = Empty_coq (* nothing gets transferred *)
      /\ lookup_map final_state.(donations_coq) sender = Just_map donation. (* donation has been accepted *)
  Proof.
    intros Hsender Hmsg Hamount Hnew_sender Hdl Hcall.
    subst;simpl in *. rewrite <- Nat.leb_le in *.
    destruct (_ <=? _);tryfalse.
    unfold inmap_map in *.
    destruct (lookup_map _ _);tryfalse. inversion Hcall;subst;clear Hcall.
    split;auto. simpl. now rewrite lookup_map_add.
  Qed.


  (** Existing donations are updated correctly in the contract's state *)

  Lemma existing_donation_correct (init_state final_state: State_coq)
        CallCtx  msg sender out_tx old_don new_don :
    (* pre-condition *)
    sender = CallCtx.(_ctx_from) -> msg = Donate_coq
    -> CallCtx.(_amount) = new_don  (* a sender donates [new_don] *)
    -> lookup_map init_state.(donations_coq) sender = Just_map old_don (* the sender has already donated before *)
    -> CallCtx.(_cur_time) <= init_state.(deadline_coq) (* deadline have not passed *)

    -> entry CallCtx init_state msg = Res_coq final_state out_tx

    (* post-condition *)
    -> out_tx = Empty_coq (* nothing gets transferred *)
      /\ lookup_map final_state.(donations_coq) sender = Just_map (new_don + old_don). (* donation has been added *)
  Proof.
    intros Hsender Hmsg Hamount Hold Hdl Hcall.
    subst;simpl in *. rewrite <- Nat.leb_le in *.
    destruct (_ <=? _);tryfalse.
    destruct (lookup_map _ _);tryfalse. inversion Hcall;subst;clear Hcall.
    split;auto. simpl. inversion Hold. subst. now rewrite lookup_map_add.
  Qed.

  Import Lia.

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

  (** The contract does no leak funds: the oveall balance before the deadline is always equal to the sum of individual donations *)

  Lemma contract_baked
    (init_state final_state: State_coq)
        CallCtx msg out_tx :
    (* pre-condition *)
      deadline_passed CallCtx.(_cur_time) init_state = false ->

      sum_map init_state.(donations_coq) = init_state.(balance_coq)

    -> entry CallCtx init_state msg = Res_coq final_state out_tx

    (* post-condition *)
    ->  sum_map final_state.(donations_coq) = final_state.(balance_coq).
  Proof.
    intros Hdl Hsum Hcall.
    destruct msg.
    + (* Donate *)
      simpl in *. unfold deadline_passed in *.
      destruct (_ <=? _);tryfalse.
      destruct (lookup_map _ _) eqn:Hlook.
      * inversion Hcall;subst;clear Hcall. simpl.
        now apply sum_map_add_in.
      * inversion Hcall;subst;clear Hcall. simpl. now apply sum_map_add_not_in.
    + (* GetFunds - it is not possible to get funds before the deadline *)
      simpl in *.
      unfold deadline_passed in *. destruct (_ <? _);tryfalse.
      destruct ( _ =? _);tryfalse.
    + (* Claim - it is not possible to claim a donation back before the deadline *)
      simpl in *. unfold deadline_passed in *.
      destruct (_ <? _);tryfalse.
  Qed.


  (** The owner gets the money after the deadline, if the goal is reached *)

  Lemma GetFunds_correct (init_state final_state: State_coq) CallCtx
        msg out_tx OwnerAddr:
    CallCtx.(_ctx_from) = OwnerAddr ->
    (* pre-condition *)
    funded CallCtx.(_cur_time) init_state = true ->
    msg = GetFunds_coq ->

    entry CallCtx init_state msg = Res_coq final_state out_tx ->

    (* post-condition *)
    out_tx = Transfer_coq init_state.(balance_coq) OwnerAddr (* the money are sent back *) /\
    final_state.(balance_coq) = 0.
  Proof.
    intros Hown Hfund Hmsg Hcall. unfold funded,deadline_passed in *. subst. simpl in *.
    destruct (_ <? _);tryfalse. destruct ( _ =? _);tryfalse. simpl in *.
    destruct (_ <=? _);tryfalse.
    inversion Hcall. easy.
  Qed.

End CrowdfundingContract.
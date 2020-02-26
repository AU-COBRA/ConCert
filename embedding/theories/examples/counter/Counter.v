(**  We develop a deep embedding of a counting contract and prove some of its functional correctness properties using the corresponding shallow embedding *)

Require Import String ZArith Basics.
From ConCert Require Import Ast Notations CustomTactics
     PCUICTranslate PCUICtoTemplate.

From ConCert Require Import Utils Prelude CounterBlockchain CounterData.

Require Import List PeanoNat ssrbool.

Import ListNotations.
From MetaCoq.Template Require Import All.

Import MonadNotation.
Import BaseTypes.
Open Scope list.

Import Lia.

Module CounterContract.
  Import CounterBlockchain.

  (** ** AST of the [init] function *)
  Module Init.
    Import Notations.
    Definition counter_init : expr :=
      [| \c : SCtx => \s : CounterValue => mkState s s |].

    Make Definition init :=
      (expr_to_tc Σ' (indexify nil counter_init)).

    Check init.
  End Init.

  (** ** AST of the [receive] function *)
  Module Receive.
  Import Notations.
  Import Prelude.
  

  Notation CCtx := "CounterContractCallContext".
  Notation CChain := "CounterChain".
  Open Scope type_scope.

  Definition increment : expr :=
    [| \chain : CChain =>  \c : CCtx => \m : Msg => \s : State =>
        let n : CounterValue := counter s in
        let b : CounterValue := blob s in
        case m : Msg return Maybe Result of
          Incr -> Just (Pair (mkState (Suc n) b) Nil) |].

  (* Compute (expr_to_tc Σ' (indexify nil increment)). *)

  Make Definition receive :=
    (expr_to_tc Σ' (indexify nil increment)).
  End Receive.
  (* Print Receive.receive. *)
End CounterContract.

Import CounterContract.

Section CounterContractExecutionExamples.
  
End CounterContractExecutionExamples.

Module CounterContractProperties.

  Import CounterBlockchain.
    Ltac inv_andb H := apply Bool.andb_true_iff in H;destruct H.
  Ltac split_andb := apply Bool.andb_true_iff;split.


  Open Scope nat.
  Open Scope bool.

  Import Lia.
  Definition counter_gt n (s : State_coq) := n <? s.(counter_coq).
  Definition counter_eq n (s : State_coq) := n =? s.(counter_coq).

  (** This function is a simplistic execution environment that performs one step of execution *)
  Definition run (receive : State_coq -> option (State_coq * list CounterActionBody) ) (init : State_coq)
    : State_coq * list CounterActionBody :=
    match receive init with
    | Some (fin, out) => (fin, out)
    | None => (init, []) (* if an error occurs, the state remains the same *)
    end.

  (** A wrapper for the assertions about the contract execution *)
  Definition assertion (pre : State_coq -> Prop)
             (entry : State_coq -> option (State_coq * list CounterActionBody))
             (post : State_coq -> list CounterActionBody -> Prop) :=
    forall init, pre init -> exists fin out, run entry init = (fin, out) /\ post fin out.

  Notation "{{ P }} c {{ Q }}" := (assertion P c Q)( at level 50).



  Lemma gt_zero_after_incr CallCtx BC (sender := CallCtx.(Ctx_from)) :
      (* pre-condition *)
      {{ fun init =>
         counter_eq 0 init }}
        (* contract call *)
       Receive.receive BC CallCtx Incr_coq

       (* post-condition *)
       {{ fun fin out => 
          counter_gt 0 fin}}.
  Proof.
  unfold assertion. intros init H.
  destruct H as [Hdl [Hgoal [Hndone Hlook]]].
  unfold counter_eq,counter_gt in *;simpl in *.
  repeat eexists.
  Qed.


  (* This lemma says if the value of the counter is n, and the contract
     is executed once, then the value is now n + 1 *)
  Lemma contract_init_incr_correct (n : nat) CallCtx BC (sender := CallCtx.(Ctx_from)) :
      (* pre-condition *)
      {{ fun init =>
         counter_eq n init }}
        (* contract call *)
       Receive.receive BC CallCtx Incr_coq
       (* post-condition *)
       {{ fun fin out => 
          counter_eq (n+1) fin}}.
  Proof.
  unfold assertion. intros init H.
  unfold counter_eq,counter_gt in *;simpl in *.
  repeat eexists; simpl. inversion H.
  apply beq_nat_true in H1.
  rewrite H1.
  rewrite Nat.add_1_r. eauto.
  Qed.
  

End CounterContractProperties.
(* In this file we prove various results about the circulation of coins in any
chain implementing a chain type. More specifically, we show that the circulation
does not change during execution of blocks. This is proven under the (implicit)
assumption that the address space is finite. *)
From Coq Require Import List Permutation ZArith Psatz Morphisms.
From SmartContracts Require Import Automation Blockchain Extras Finite ChainedList.
From RecordUpdate Require Import RecordSet.
Import ListNotations.

Section Circulation.
Context {ChainBase : ChainBase}.
Context `{Finite Address}.

Local Open Scope Z.
Definition circulation (chain : Chain) :=
  sumZ (account_balance chain) (elements Address).

(* We then prove that over any single action, the circulation is preserved.
The idea behind this proof is that addrs contain from and to so
we can move them to the beginning of the sum and it easily follows that
the sum of their balances is the same as before. For the rest of the
list the total balance will then not be affected which follows by induction. *)
Lemma address_reorganize {a b : Address} :
  a <> b ->
  exists suf, Permutation ([a; b] ++ suf) (elements Address).
Proof.
  intros a_neq_b.
  apply (NoDup_incl_reorganize _ [a; b]);
    repeat constructor; unfold incl; auto.
  intros Hin.
  cbn in *.
  intuition.
Qed.

Lemma eval_action_from_to_same
      {pre : Environment}
      {act : Action}
      {post : Environment}
      {new_acts : list Action}
      (eval : ActionEvaluation pre act post new_acts) :
  eval_from eval = eval_to eval ->
  circulation post = circulation pre.
Proof.
  intros from_eq_to.
  unfold circulation.
  induction (elements Address) as [| x xs IH].
  - reflexivity.
  - cbn in *.
    rewrite IH, (account_balance_post eval), from_eq_to.
    lia.
Qed.

Hint Resolve eval_action_from_to_same : core.

Lemma eval_action_circulation_unchanged
      {pre : Environment}
      {act : Action}
      {post : Environment}
      {new_acts : list Action} :
  ActionEvaluation pre act post new_acts ->
  circulation post = circulation pre.
Proof.
  intros eval.
  destruct (address_eqb_spec (eval_from eval) (eval_to eval))
    as [from_eq_to | from_neq_to]; eauto.
  destruct (address_reorganize from_neq_to) as [suf perm].
  apply Permutation_sym in perm.
  unfold circulation.
  rewrite 2!(sumZ_permutation perm).
  cbn.
  rewrite (account_balance_post_to eval from_neq_to).
  rewrite (account_balance_post_from eval from_neq_to).
  enough (sumZ (account_balance pre) suf = sumZ (account_balance post) suf) by lia.

  pose proof (Permutation_NoDup perm) as perm_set.
  assert (from_not_in_suf: ~In (eval_from eval) suf).
  { apply (in_NoDup_app _ [eval_from eval; eval_to eval] _); intuition. }
  assert (to_not_in_suf: ~In (eval_to eval) suf).
  { apply (in_NoDup_app _ [eval_from eval; eval_to eval] _); intuition. }

  clear perm perm_set.
  pose proof (account_balance_post_irrelevant eval) as balance_irrel.
  induction suf as [| x xs IH]; auto.
  cbn in *.
  rewrite IH, balance_irrel; auto.
Qed.

Hint Resolve eval_action_circulation_unchanged : core.

Instance circulation_proper :
  Proper (ChainEquiv ==> eq) circulation.
Proof.
  intros x y [].
  unfold circulation, account_balance.
  induction (elements Address) as [|z zs IH]; auto.
  cbn.
  now
    repeat
    match goal with
    | [H: _ |- _] => rewrite H
  end.
Qed.

Lemma circulation_add_new_block header baker env :
  circulation (add_new_block header baker env) =
  (circulation env + compute_block_reward (block_height header))%Z.
Proof.
  assert (Hperm: exists suf, Permutation ([baker] ++ suf) (elements Address)).
  { apply NoDup_incl_reorganize; repeat constructor; unfold incl; auto. }
  destruct Hperm as [suf perm].
  symmetry in perm.
  pose proof (Permutation_NoDup perm (elements_set Address)) as perm_set.
  unfold circulation.
  rewrite perm.
  cbn.
  unfold add_balance.
  rewrite address_eq_refl.
  match goal with
  | [|- ?a + ?b + ?c = ?b + ?d + ?a] => enough (c = d) by lia
  end.

  pose proof (in_NoDup_app baker [baker] suf ltac:(intuition) perm_set) as not_in_suf.
  clear perm perm_set.
  induction suf as [| x xs IH]; auto.
  cbn in *.
  apply Decidable.not_or in not_in_suf.
  destruct (address_eqb_spec x baker); try tauto.
  specialize (IH (proj2 not_in_suf)).
  lia.
Qed.

Lemma step_circulation {prev next} (step : ChainStep prev next) :
  circulation next =
  match step with
  | step_block _ _ _ _ =>
    circulation prev + compute_block_reward (block_height (block_header next))
  | _ => circulation prev
  end%Z.
Proof.
  destruct step;
    repeat
      match goal with
      | [H: EnvironmentEquiv _ _ |- _] => rewrite H in *; clear H
      end.
  - (* New block *)
    now rewrite circulation_add_new_block.
  - (* New action *)
    erewrite eval_action_circulation_unchanged; eauto.
  - (* Permute queue *)
    intuition.
Qed.

Theorem chain_trace_circulation
        {state : ChainState} :
  reachable state ->
  circulation state =
  sumZ compute_block_reward (seq 1 (block_height (block_header state))).
Proof.
  intros [trace].
  remember empty_state as from eqn:eq.
  induction trace as [| from mid to xs IH x]; rewrite eq in *; clear eq.
  - unfold circulation.
    induction (elements Address); auto.
  - rewrite (step_circulation x).
    destruct x.
    + rewrite_environment_equiv.
      cbn.
      unfold constructor.
      match goal with
      | [H: IsValidNextBlock _ _ |- _] =>
        rewrite (proj1 H), IH, sumZ_seq_S; auto
      end.
    + erewrite block_header_post_action; eauto.
    + intuition.
Qed.
End Circulation.

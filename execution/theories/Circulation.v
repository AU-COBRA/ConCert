(* In this file we prove that the circulation of any blockchain implementing our
semantics is as expected: the sum of all rewards paid out in blocks. *)
From Coq Require Import List.
From Coq Require Import Permutation.
From Coq Require Import ZArith.
From Coq Require Import Psatz.
From Coq Require Import Morphisms.
From ConCert.Utils Require Import Automation.
From ConCert.Utils Require Import Extras.
From ConCert.Execution Require Import Blockchain.
From ConCert.Execution Require Import Finite.
Import ListNotations.

Section Circulation.
Context {ChainBase : ChainBase}.
Context `{Finite Address}.

Local Open Scope Z.
Definition circulation (env : Environment) :=
  sumZ (env_account_balances env) (elements Address).

(* We prove first that over any single action, the circulation is preserved.
The idea behind this proof is that addrs contain from and to, so
we can move them to the beginning of the sum, and it easily follows that
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
  now destruct_or_hyps.
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

Local Hint Resolve eval_action_from_to_same : core.

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
  enough (sumZ (env_account_balances pre) suf = sumZ (env_account_balances post) suf)
    by lia.

  pose proof (Permutation_NoDup perm) as perm_set.
  assert (from_not_in_suf: ~In (eval_from eval) suf).
  { apply (in_NoDup_app _ [eval_from eval; eval_to eval] _); auto with datatypes. }
  assert (to_not_in_suf: ~In (eval_to eval) suf).
  { apply (in_NoDup_app _ [eval_from eval; eval_to eval] _); auto with datatypes. }

  clear perm perm_set.
  pose proof (account_balance_post_irrelevant eval) as balance_irrel.
  induction suf as [| x xs IH]; auto.
  cbn in *.
  rewrite IH, balance_irrel; auto.
Qed.

Local Hint Resolve eval_action_circulation_unchanged : core.

Instance circulation_proper :
  Proper (EnvironmentEquiv ==> eq) circulation.
Proof.
  intros x y [].
  unfold circulation, env_account_balances.
  induction (elements Address) as [|z zs IH]; auto.
  cbn.
  now
    repeat
    match goal with
    | [H: _ |- _] => rewrite H
  end.
Qed.


(* Now we prove that adding a block _does_ increase the circulation
by what we would expect. *)
Lemma circulation_add_new_block header env :
  circulation (add_new_block_to_env header env) =
  (circulation env + block_reward header)%Z.
Proof.
  assert (Hperm: exists suf, Permutation ([block_creator header] ++ suf) (elements Address)).
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

  pose proof (in_NoDup_app
                (block_creator header)
                [block_creator header] suf ltac:(auto with datatypes) perm_set) as not_in_suf.
  clear perm perm_set.
  induction suf as [| x xs IH]; auto.
  cbn in *.
  apply Decidable.not_or in not_in_suf.
  destruct (address_eqb_spec x (block_creator header)); try tauto.
  specialize (IH (proj2 not_in_suf)).
  lia.
Qed.

(* We then get a lemma over steps *)
Lemma step_circulation {prev next} (step : ChainStep prev next) :
  circulation next =
  match step with
  | step_block _ _ header _ _ _ _ _ =>
    circulation prev + block_reward header
  | _ => circulation prev
  end%Z.
Proof.
  destruct_chain_step; try rewrite_environment_equiv.
  - (* New block *)
    now rewrite circulation_add_new_block.
  - (* New action *)
    erewrite eval_action_circulation_unchanged; eauto.
  - (* Invalid User Action *)
    reflexivity.
  - (* Permute queue *)
    reflexivity.
Qed.

(* And combining these gives the final result. *)
Theorem chain_trace_circulation
        {state : ChainState}
        (trace : ChainTrace empty_state state) :
  circulation state = sumZ block_reward (trace_blocks trace).
Proof.
  remember empty_state as from eqn:eq.
  induction trace as [| from mid to xs IH x]; subst.
  - unfold circulation.
    induction (elements Address); auto.
  - rewrite (step_circulation x).
    cbn.
    destruct_chain_step; auto.
    cbn.
    rewrite <- IH by auto.
    lia.
Qed.
End Circulation.

(* In this file we prove various results about the circulation of coins in any
chain implementing a chain type. More specifically, we show that the circulation
does not change during execution of blocks. This is proven under the (implicit)
assumption that the address space is finite. *)
From Coq Require Import List Permutation ZArith Psatz.
From SmartContracts Require Import Automation Blockchain Extras Finite.
From RecordUpdate Require Import RecordSet.
Import ListNotations.

Section Circulation.
Context {ChainBaseTypes : ChainBaseTypes}.
Context `{Finite Address}.

Definition circulation (chain : Chain) :=
  sumZ (account_balance chain) (elements Address).

Definition coins_created (start_height end_height : nat) : Amount :=
  sumZ compute_block_reward (seq (S start_height) (end_height - start_height)).

(* We then prove that over any single step, the circulation is preserved.
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
    repeat constructor; unfold incl; prove.
Qed.

Lemma step_from_to_same
      {pre : Environment}
      {act : Action}
      {tx : Tx}
      {post : Environment}
      {new_acts : list Action}
      (step : ChainStep pre act tx post new_acts) :
  tx_from tx = tx_to tx ->
  circulation post = circulation pre.
Proof.
  intros from_eq_to.
  unfold circulation.
  induction (elements Address) as [| x xs IH].
  - reflexivity.
  - simpl in *.
    rewrite IH, (account_balance_post step), from_eq_to.
    lia.
Qed.

Hint Resolve step_from_to_same : core.

Lemma step_circulation_unchanged
      {pre : Environment}
      {act : Action}
      {tx : Tx}
      {post : Environment}
      {new_acts : list Action}
      (step : ChainStep pre act tx post new_acts) :
  circulation post = circulation pre.
Proof.
  destruct (address_eqb_spec (tx_from tx) (tx_to tx))
    as [from_eq_to | from_neq_to]; eauto.
  destruct (address_reorganize from_neq_to) as [suf perm].
  apply Permutation_sym in perm.
  unfold circulation.
  rewrite 2!(sumZ_permutation perm); prove.
  rewrite (account_balance_post_to step from_neq_to).
  rewrite (account_balance_post_from step from_neq_to).
  enough (sumZ (account_balance pre) suf = sumZ (account_balance post) suf) by prove.

  pose proof (Permutation_NoDup perm) as perm_set.
  assert (from_not_in_suf: ~In (tx_from tx) suf).
  { apply (in_NoDup_app _ [tx_from tx; tx_to tx] _); prove. }
  assert (to_not_in_suf: ~In (tx_to tx) suf).
  { apply (in_NoDup_app _ [tx_from tx; tx_to tx] _); prove. }

  clear perm perm_set.
  pose proof (account_balance_post_irrelevant step).
  induction suf as [| x xs IH]; prove.
Qed.

Hint Resolve step_circulation_unchanged : core.

(* Finally, we get the result over block traces by a simple induction. *)
Lemma block_trace_circulation_unchanged
      {bef : list Action}
      {after : list Action}
      {post pre : Environment}
      (trace : BlockTrace pre bef post after)
  : circulation post = circulation pre.
Proof.
  induction trace;
    match goal with
    | [IH: _ |- _] => try rewrite IH; eauto
    end.
Qed.

Hint Resolve block_trace_circulation_unchanged : core.

Lemma circulation_equal (c1 c2 : Chain) :
  ChainEquiv c1 c2 -> circulation c1 = circulation c2.
Proof.
  intros [].
  unfold circulation, account_balance.
  induction (elements Address); prove.
Qed.

Lemma circulation_add_new_block header baker env :
  circulation (add_new_block header baker env) =
  (circulation env + compute_block_reward (block_height header))%Z.
Proof.
  assert (Hperm: exists suf, Permutation ([baker] ++ suf) (elements Address)).
  { apply NoDup_incl_reorganize; repeat constructor; unfold incl; prove. }
  destruct Hperm as [suf perm].
  symmetry in perm.
  pose proof (Permutation_NoDup perm (elements_set Address)) as perm_set.
  unfold circulation.
  rewrite perm.
  simpl.
  unfold constructor, set, account_balance.
  simpl.
  destruct (address_eqb_spec baker baker); try congruence.
  simpl.
  pose proof (in_NoDup_app baker [baker] suf ltac:(prove) perm_set) as not_in_suf.
  repeat rewrite <- Z.add_assoc.
  f_equal.
  rewrite <- Z.add_comm.
  repeat rewrite <- Z.add_assoc.
  f_equal.

  clear perm perm_set e.
  induction suf as [| x xs IH]; auto.
  simpl in *.
  apply Decidable.not_or in not_in_suf.
  destruct (address_eqb_spec x baker); try tauto.
  specialize (IH (proj2 not_in_suf)).
  lia.
Qed.

Theorem chain_trace_circulation
      {env_start env_end : Environment}
      (trace : ChainTrace env_start env_end)
  : circulation env_end =
    (circulation env_start +
     coins_created
       (block_height (block_header env_start))
       (block_height (block_header env_end)))%Z.
Proof.
  unfold coins_created.
  induction trace as
      [|prev_start prev_end header baker acts block_start new_end prev_trace IH valid block_trace eq].
  - rewrite Nat.sub_diag.
    simpl. lia.
  - unfold IsValidNextBlock in valid.
    rewrite (block_header_post_steps block_trace).
    rewrite (chain_equiv _ _ eq).
    simpl.
    rewrite (proj1 valid).
    unfold coins_created.
    pose proof (block_height_post_trace prev_trace) as height_le.
    match goal with
    | [|- context[S ?a - ?b]] => replace (S a - b) with (S (a - b)) by lia
    end.
    rewrite sumZ_seq_S.
    unfold coins_created in IH.
    rewrite Z.add_assoc, <- IH.
    match goal with
    | [|- context[S ?a + (?b - ?a)]] => replace (S a + (b - a)) with (S b) by lia
    end.
    rewrite (block_trace_circulation_unchanged block_trace).
    rewrite (circulation_equal _ _ eq).
    rewrite circulation_add_new_block.
    now rewrite (proj1 valid).
Qed.
End Circulation.

From Coq Require Import List.
From Coq Require Import Morphisms.
From Coq Require Import Orders.
From Coq Require Import ZArith.
From Coq Require Import Znumtheory.
From Coq Require Import Permutation.
From Coq Require Import Psatz.
From Coq Require Import Mergesort.
From Coq Require Program.
From RecordUpdate Require Import RecordUpdate.
Require Import Automation.
Require Import Blockchain.
Require Import BoundedN.
Require Import Containers.
From stdpp Require countable.
Require ContractMonads.
Require Import Extras.
Require Import BoardroomMath.
Require Import Monads.
Require Import Serializable.

Import ListNotations.
Import RecordSetNotations.
Import BoardroomMathNotations.

Section BoardroomVoting.
Context `{Base : ChainBase}.

Context {A : Type}.
Context (H : list positive -> positive).
Context {ser : Serializable A}.
Context {axioms : BoardroomAxioms A}.
Context {gen : Generator _}.
Context {discr_log : DiscreteLog _ _}.

(* Allow us to automatically derive Serializable instances *)
Set Nonrecursive Elimination Schemes.

Record Setup :=
  build_setup {
    eligible_voters : FMap Address unit;
    finish_registration_by : nat;
    finish_commit_by : option nat;
    finish_vote_by : nat;
    registration_deposit : Amount;
  }.


Record VoterInfo :=
  build_voter_info {
    voter_index : nat;
    vote_hash : positive;
    public_vote : A;
}.

Record State :=
  build_state {
    owner : Address;
    registered_voters : FMap Address VoterInfo;
    public_keys : list A;
    setup : Setup;
    result : option nat;
  }.

(* w, a1, b1, a2, b2, d1, d2 *)
Definition VoteProof := (Z * A * A * A * A * Z * Z * Z * Z)%type.

Inductive Msg :=
| signup (pk : A) (proof : A * Z)
| commit_to_vote (hash : positive)
| submit_vote (v : A) (proof : VoteProof)
| tally_votes.

Global Instance VoterInfo_settable : Settable _ :=
  settable! build_voter_info <voter_index; vote_hash; public_vote>.

Global Instance State_settable : Settable _ :=
  settable! build_state <owner; registered_voters; public_keys; setup; result>.

Global Instance Setup_serializable : Serializable Setup :=
  Derive Serializable Setup_rect<build_setup>.

Global Instance VoterInfo_serializable : Serializable VoterInfo :=
  Derive Serializable VoterInfo_rect<build_voter_info>.

Global Instance State_serializable : Serializable State :=
  Derive Serializable State_rect<build_state>.

Global Instance Msg_serializable : Serializable Msg :=
  Derive Serializable Msg_rect<signup, commit_to_vote, submit_vote, tally_votes>.

Import ContractMonads.

Local Open Scope broom.

Definition hash_sk_data (gv pk : A) (i : nat) : positive :=
  H [countable.encode (generator : A); countable.encode gv; countable.encode pk; countable.encode i].

(* This follows the original open vote protocol paper. It is a schnorr signature
     with the fiat-shamir heuristic applied. *)
Definition secret_key_proof (sk : Z) (v : Z) (i : nat) : A * Z :=
  let gv : A := generator^v in
  let pk := compute_public_key sk in
  let z := Zpos (hash_sk_data gv pk i) in
  let r := (v - sk * z)%Z in
  (gv, r).

Definition verify_secret_key_proof (pk : A) (i : nat) (proof : A * Z) : bool :=
  let (gv, r) := proof in
  let z := Zpos (hash_sk_data gv pk i) in
  elmeqb gv (generator^r * (pk^z)).

Definition hash_sv_data (i : nat) (pk rk a1 b1 a2 b2 : A) : positive :=
  H (countable.encode i :: map countable.encode [pk; rk; a1; b1; a2; b2]).

Definition secret_vote_proof (sk : Z) (rk : A) (sv : bool) (i : nat) (w r d : Z) : VoteProof :=
  let pk : A := compute_public_key sk in
  let pv : A := compute_public_vote rk sk sv in
  if sv then
    let a1 : A := generator^r * pk^d in
    let b1 : A := rk^r * pv^d in
    let a2 : A := generator^w in
    let b2 : A := rk^w in
    let c := Zpos (hash_sv_data i pk rk a1 b1 a2 b2) in
    let d2 := c - d in
    let r2 := w - sk*d2 in
    (w, a1, b1, a2, b2, d, d2, r, r2)
  else
    let a1 := generator^w in
    let b1 := rk^w in
    let a2 := generator^r * pk^d in
    let b2 := rk^r * (pv * inv generator)^d in
    let c := Zpos (hash_sv_data i pk rk a1 b1 a2 b2) in
    let d1 := c - d in
    let r1 := w - sk*d1 in
    (w, a1, b1, a2, b2, d1, d, r1, r).

Local Open Scope bool.
Definition verify_secret_vote_proof (pk rk pv : A) (i : nat) (proof : VoteProof) : bool :=
  let '(w, a1, b1, a2, b2, d1, d2, r1, r2) := proof in
  let c := hash_sv_data i pk rk a1 b1 a2 b2 in
  (Zpos c =? d1 + d2)%Z &&
  (a1 =? generator^r1 * pk^d1)%broom &&
  (b1 =? rk^r1 * pv^d1)%broom &&
  (a2 =? generator^r2 * pk^d2)%broom &&
  (b2 =? rk^r2 * (pv * inv generator)^d2)%broom.

Definition make_signup_msg (sk : Z) (v : Z) (i : nat) : Msg :=
  signup (compute_public_key sk) (secret_key_proof sk v i).

Definition make_commit_msg (pks : list A) (my_index : nat) (sk : Z) (sv : bool) : Msg :=
  let pv := compute_public_vote (reconstructed_key pks my_index) sk sv in
  commit_to_vote (H [countable.encode pv]).

Definition make_vote_msg (sk : Z) (rk : A) (sv : bool) (my_index : nat) (w r d : Z) : Msg :=
  submit_vote (compute_public_vote rk sk sv)
              (secret_vote_proof sk rk sv my_index w r d).

Definition init : ContractIniter Setup State :=
  do owner <- lift caller_addr;
  do setup <- deployment_setup;
  do lift (if finish_registration_by setup <? finish_vote_by setup then Some tt else None)%nat;
  accept_deployment
    {| owner := owner;
       registered_voters := FMap.empty;
       public_keys := [];
       setup := setup;
       result := None; |}.

Definition receive : ContractReceiver State Msg State :=
  do state <- my_state;
  do caller <- lift caller_addr;
  do cur_slot <- lift current_slot;
  do msg <- call_msg >>= lift;
  match msg with
  | signup pk prf =>
    do lift (if finish_registration_by (setup state) <? cur_slot then None else Some tt)%nat;
    do lift (if FMap.find caller (eligible_voters (setup state)) then Some tt else None);
    do lift (if FMap.find caller (registered_voters state) then None else Some tt);
    do amt <- lift call_amount;
    do lift (if (amt =? (registration_deposit (setup state)))%Z then Some tt else None);
    do lift (if Z.of_nat (length (public_keys state)) <? order - 2 then Some tt else None);
    let index := length (public_keys state) in
    do lift (if verify_secret_key_proof pk index prf then Some tt else None);
    let inf := {| voter_index := index;
                  vote_hash := 1%positive;
                  public_vote := zero; |} in
    let new_state := state<|registered_voters ::= FMap.add caller inf|>
                          <|public_keys ::= fun l => l ++ [pk]|> in
    accept_call new_state

  | commit_to_vote hash =>
    do commit_by <- lift (finish_commit_by (setup state));
    do lift (if commit_by <? cur_slot then None else Some tt)%nat;
    do inf <- lift (FMap.find caller (registered_voters state));
    let inf := inf<|vote_hash := hash|> in
    accept_call (state<|registered_voters ::= FMap.add caller inf|>)

  | submit_vote v proof =>
    do lift (if finish_vote_by (setup state) <? cur_slot then None else Some tt)%nat;
    do inf <- lift (FMap.find caller (registered_voters state));
    do lift (if finish_commit_by (setup state) then
               if (H [countable.encode v] =? vote_hash inf)%positive then Some tt else None
             else
               Some tt);
    do lift (if verify_secret_vote_proof
                  (nth (voter_index inf) (public_keys state) 0)
                  (reconstructed_key (public_keys state) (voter_index inf))
                  v
                  (voter_index inf)
                  proof then Some tt else None);
    let inf := inf<|public_vote := v|> in
    accept_call (state<|registered_voters ::= FMap.add caller inf|>)

  | tally_votes =>
    do lift (if cur_slot <? finish_vote_by (setup state) then None else Some tt)%nat;
    do lift (match result state with | Some _ => None | None => Some tt end);
    let voters := FMap.values (registered_voters state) in
    do lift (if existsb
                  (fun vi => if elmeqb (public_vote vi) zero then true else false)
                  voters then None else Some tt);
    let votes := map public_vote voters in
    do res <- lift (bruteforce_tally votes);
    accept_call (state<|result := Some res|>)
  end.

Definition boardroom_voting : Contract Setup Msg State.
Proof with cbn -[Nat.ltb].
  refine (build_contract init receive _ _).
  - repeat intro; subst.
    cbn -[Nat.ltb].
    destruct (_ <? _)%nat; auto.
  - intros c1 c2 ceq ctx ? <- state ? <- msg ? <-.
    unfold run_contract_receiver...
    destruct msg as [msg|]; [|congruence]...
    destruct msg.
    + rewrite <- ceq.
      destruct (_ <? _)%nat; auto.
      destruct (FMap.find _ _); auto.
      destruct (FMap.find _ _); auto.
      destruct (_ =? _)%Z; auto.
      destruct (_ <? _); auto.
      destruct (verify_secret_key_proof _ _ _); auto.
    + destruct (finish_commit_by _); auto.
      rewrite <- ceq.
      destruct (_ <? _)%nat; auto.
      destruct (FMap.find _ _); auto.
    + rewrite <- ceq.
      destruct (_ <? _)%nat; auto.
      destruct (FMap.find _ _); auto.
      destruct (finish_commit_by _); [destruct (_ =? _)%positive; auto|].
      all: destruct (verify_secret_vote_proof _ _ _ _); auto.
    + rewrite <- ceq.
      destruct (_ <? _)%nat; auto.
      destruct (result _); auto.
      destruct (existsb _ _); auto.
      destruct (bruteforce_tally _); auto.
Defined.

Section Theories.

Record SecretVoterInfo :=
  build_secret_voter_info {
    svi_index : nat;
    (* Secret key *)
    svi_sk : Z;
    (* Chosen randomness for knowledge of secret key proof *)
    svi_sk_r : Z;
    (* Secret vot e*)
    svi_sv : bool;
    (* Chosen random w for vote proof *)
    svi_sv_w : Z;
    (* Chosen random r for vote proof *)
    svi_sv_r : Z;
    (* Chosen random d for vote proof *)
    svi_sv_d : Z;
  }.

Global Instance SecretVoterInfo_settable : Settable _ :=
  settable! build_secret_voter_info <svi_index; svi_sk; svi_sk_r;
                                     svi_sv; svi_sv_w; svi_sv_r; svi_sv_d>.

(* For correctness we assume that all signups and vote messages were
   created using the make_signup_msg and make_vote_msg functions from
   the contract *)
Fixpoint MsgAssumption
         (pks : list A)
         (parties : Address -> SecretVoterInfo)
         (calls : list (ContractCallInfo Msg)) : Prop :=
  match calls with
  | call :: calls =>
    let party := parties (Blockchain.call_from call) in
    match Blockchain.call_msg call with
    | Some (signup pk prf as m) => m = make_signup_msg (svi_sk party) (svi_sk_r party)
                                                       (svi_index party)
    | Some (submit_vote _ _ as m) =>
      m = make_vote_msg (svi_sk party)
                        (reconstructed_key pks (svi_index party))
                        (svi_sv party)
                        (svi_index party)
                        (svi_sv_w party)
                        (svi_sv_r party)
                        (svi_sv_d party)
    | _ => True
    end /\ MsgAssumption pks parties calls
  | [] => True
  end.

Definition signups (calls : list (ContractCallInfo Msg)) : list (Address * A) :=
  (* reverse the signups since the calls will have the last one at the head *)
  rev (map_option (fun call => match Blockchain.call_msg call with
                               | Some (signup pk prf) => Some (Blockchain.call_from call, pk)
                               | _ => None
                               end) calls).

(* The index map and public keys list provided also needs to match the
   order in which parties signed up in the contract. *)
Definition SignupOrderAssumption
           (pks : list A)
           (parties : Address -> SecretVoterInfo)
           (calls : list (ContractCallInfo Msg)) : Prop :=
  All (fun '((addr, pk), i) => svi_index (parties addr) = i /\ nth_error pks i = Some pk)
      (zip (signups calls) (seq 0 (length (signups calls)))).

Local Open Scope nat.

Lemma no_outgoing bstate caddr :
  reachable bstate ->
  env_contracts bstate caddr = Some (boardroom_voting : WeakContract) ->
  outgoing_acts bstate caddr = [].
Proof.
  contract_induction; intros; cbn -[Nat.ltb] in *; auto.
  - now inversion IH.
  - destruct msg as [msg|]; cbn -[Nat.ltb] in *; try congruence.
    destruct msg.
    + destruct (_ <? _); cbn in *; try congruence.
      destruct (FMap.find _ _); cbn in *; try congruence.
      destruct (FMap.find _ _); cbn in *; try congruence.
      destruct (_ =? _)%Z; cbn in *; try congruence.
      destruct (_ <? _)%Z; cbn in *; try congruence.
      destruct (verify_secret_key_proof _ _ _); cbn in *; try congruence.
      now inversion_clear receive_some.
    + destruct (finish_commit_by _); cbn -[Nat.ltb] in *; try congruence.
      destruct (_ <? _); cbn in *; try congruence.
      destruct (FMap.find _ _); cbn in *; try congruence.
      now inversion_clear receive_some.
    + destruct (_ <? _); cbn in *; try congruence.
      destruct (FMap.find _ _); cbn in *; try congruence.
      destruct (if finish_commit_by _ then _ else _); cbn in *; try congruence.
      destruct (verify_secret_vote_proof _ _ _ _); cbn in *; try congruence.
      now inversion_clear receive_some.
    + destruct (_ <? _); cbn in *; try congruence.
      destruct (result _); cbn in *; try congruence.
      destruct (existsb _ _); cbn in *; try congruence.
      destruct (bruteforce_tally _); cbn in *; try congruence.
      now inversion_clear receive_some.
  - inversion IH.
  - subst out_queue.
    now apply Permutation_nil in perm.
  - [AddBlockFacts]: exact (fun _ _ _ _ _ _ => True).
    [DeployFacts]: exact (fun _ _ => True).
    [CallFacts]: exact (fun _ _ _ => True).
    unset_all; subst.
    destruct_chain_step; auto.
    destruct_action_eval; auto.
Qed.

Lemma Permutation_modify k vold vnew (m : FMap Address VoterInfo) :
  FMap.find k m = Some vold ->
  voter_index vold = voter_index vnew ->
  Permutation (map (fun '(_, v) => voter_index v)
                   (FMap.elements m))
              (seq 0 (FMap.size m)) ->
  Permutation
    (map (fun '(_, v0) => voter_index v0)
         (FMap.elements (FMap.add k vnew m)))
    (seq 0 (FMap.size m)).
Proof.
  intros find_some index old_perm.
  rewrite <- old_perm.
  rewrite <- (FMap.add_id _ _ _ find_some) at 2.
  rewrite <- (FMap.add_remove k vold).
  rewrite (FMap.elements_add_existing k vold vnew) by auto.
  rewrite FMap.elements_add by auto.
  cbn.
  now rewrite index.
Qed.

Lemma all_signups pks parties calls :
  SignupOrderAssumption pks parties calls ->
  length (signups calls) = length pks ->
  map snd (signups calls) = pks.
Proof.
  intros order len_signups.
  unfold SignupOrderAssumption in order.
  revert parties pks len_signups order.
  induction (signups calls) as [|[addr pk] xs IH]; intros parties pks len_signups order.
  - destruct pks; cbn in *; congruence.
  - cbn in *.
    destruct pks as [|pk' pks]; cbn in *; try lia.
    destruct order as [[index_eq nth_eq] all].
    f_equal; try congruence.
    apply (IH (fun addr => (parties addr)<|svi_index ::= fun i => i - 1|>));
      [lia|].
    clear -all.
    rewrite <- (map_id xs) in all at 1.
    rewrite <- seq_shift in all.
    rewrite zip_map in all.
    apply All_map in all.
    apply (All_ext_in _ _ _ all).
    intros.
    destruct a, p.
    cbn in *.
    split; [|tauto].
    destruct H0; lia.
Qed.

Local Open Scope broom.
Lemma elmeqb_eq (a a' : A) :
  (a =? a') = true <-> a == a'.
Proof.
  destruct (elmeqb_spec a a'); [tauto|].
  split; congruence.
Qed.

Hint Resolve
     pow_nonzero generator_nonzero int_domain generator_nonzero compute_public_key_unit
     reconstructed_key_unit
  : broom.
Lemma verify_secret_key_proof_spec sk v i :
  verify_secret_key_proof (compute_public_key sk) i (secret_key_proof sk v i) = true.
Proof with auto with broom.
  cbn.
  apply elmeqb_eq.
  apply log_both...
  rewrite log_pow...
  rewrite log_mul...
  unfold "exp=".
  assert (order - 1 <> 0)%Z by (pose proof order_ge_2; lia).
  rewrite Z.add_mod...
  rewrite !log_pow...
  rewrite log_generator.
  rewrite !Z.mul_1_r.
  unfold compute_public_key.
  rewrite <- Z.mul_mod_idemp_r...
  rewrite log_pow...
  rewrite log_generator.
  rewrite Z.mul_1_r.
  rewrite Z.mul_mod_idemp_r...
  rewrite <- Z.add_mod...
  f_equal.
  lia.
Qed.

Lemma verify_secret_vote_proof_spec sk pks sv i w r d :
  All (fun pk => pk !== 0) pks ->
  verify_secret_vote_proof
    (compute_public_key sk)
    (reconstructed_key pks i)
    (compute_public_vote (reconstructed_key pks i) sk sv)
    i
    (secret_vote_proof sk (reconstructed_key pks i) sv i w r d) = true.
Proof.
  intros all_units.
  set (rk := reconstructed_key pks i).
  unfold verify_secret_vote_proof, secret_vote_proof.
  cbn.
  destruct sv.
  - set (h := hash_sv_data _ _ _ _ _ _ _).
    rewrite Zplus_minus.
    rewrite Pos.eqb_refl, !elmeqb_refl.
    cbn.
    unfold compute_public_key.
    rewrite pow_pow by (auto with broom).
    rewrite <- pow_plus by (auto with broom).
    rewrite Z.sub_add.
    rewrite elmeqb_refl.
    cbn.
    unfold compute_public_vote.
    rewrite <- (mul_assoc (rk^sk)).
    rewrite (mul_comm generator).
    rewrite inv_inv_l by (auto with broom).
    rewrite (mul_comm (rk^sk)), mul_1_l.
    rewrite pow_pow by (subst rk; auto with broom).
    rewrite <- pow_plus by (subst rk; auto with broom).
    rewrite Z.sub_add.
    now rewrite elmeqb_refl.
  - set (h := hash_sv_data _ _ _ _ _ _ _).
    rewrite Z.sub_add.
    rewrite Pos.eqb_refl, !elmeqb_refl.
    cbn.
    unfold compute_public_key.
    rewrite pow_pow by (auto with broom).
    rewrite <- pow_plus by (auto with broom).
    rewrite Z.sub_add.
    rewrite elmeqb_refl.
    cbn.
    unfold compute_public_vote.
    rewrite (mul_comm (rk^sk)), mul_1_l.
    rewrite pow_pow by (subst rk; auto with broom).
    rewrite <- pow_plus by (subst rk; auto with broom).
    rewrite Z.sub_add.
    now rewrite elmeqb_refl.
Qed.

Definition has_tallied (calls : list (ContractCallInfo Msg)) : bool :=
  existsb (fun c => match Blockchain.call_msg c with
                    | Some tally_votes => true
                    | _ => false
                    end) calls.

Theorem boardroom_voting_correct_strong
        (bstate : ChainState)
        (caddr : Address)
        (trace : ChainTrace empty_state bstate)
        (parties : Address -> SecretVoterInfo)
        (pks : list A) :
    env_contracts bstate caddr = Some (boardroom_voting : WeakContract) ->
    exists (cstate : State)
           (depinfo : DeploymentInfo Setup)
           (inc_calls : list (ContractCallInfo Msg)),
      deployment_info Setup trace caddr = Some depinfo /\
      contract_state bstate caddr = Some cstate /\
      incoming_calls Msg trace caddr = Some inc_calls /\

      finish_registration_by (setup cstate) < finish_vote_by (setup cstate) /\

      (Blockchain.current_slot bstate < finish_vote_by (setup cstate) ->
       has_tallied inc_calls = false) /\

      length (public_keys cstate) = FMap.size (registered_voters cstate) /\
      public_keys cstate = map snd (signups inc_calls) /\

      (Z.of_nat (length (public_keys cstate)) < order - 1)%Z /\

      (MsgAssumption pks parties inc_calls ->
       SignupOrderAssumption pks parties inc_calls ->
       (finish_registration_by (setup cstate) < Blockchain.current_slot bstate ->
        length pks = length (signups inc_calls)) ->

       Permutation (map (fun '(_, v) => voter_index v)
                        (FMap.elements (registered_voters cstate)))
                   (seq 0 (length (public_keys cstate))) /\

       (forall addr inf,
           FMap.find addr (registered_voters cstate) = Some inf ->
           voter_index inf < length (public_keys cstate) /\
           voter_index inf = svi_index (parties addr) /\
           nth_error (public_keys cstate) (voter_index inf) =
           Some (compute_public_key (svi_sk (parties addr))) /\
           (public_vote inf == zero \/
            public_vote inf = compute_public_vote
                                (reconstructed_key pks (voter_index inf))
                                (svi_sk (parties addr))
                                (svi_sv (parties addr)))) /\
       ((has_tallied inc_calls = false ->
         result cstate = None) /\
        (has_tallied inc_calls = true ->
         result cstate = Some (sumnat (fun party => if svi_sv (parties party) then 1 else 0)%nat
                                     (FMap.keys (registered_voters cstate)))))).
Proof.
  contract_induction; intros.
  - [AddBlockFacts]: exact (fun _ old_slot _ _ new_slot _ => old_slot < new_slot).
    subst AddBlockFacts.
    cbn in facts.
    destruct_and_split; try tauto.
    + eauto with lia.
    + intros; eauto with lia.
  - cbn -[Nat.ltb] in *.
    destruct (_ <? _) eqn:ltb; [|congruence].
    apply Nat.ltb_lt in ltb.
    inversion_clear init_some.
    cbn.
    split; auto.
    split; auto.
    split; [symmetry; apply FMap.size_empty|].
    pose proof order_ge_2.
    split; [auto|].
    split; [lia|].
    intros _ index_assum pks_assum.
    rewrite FMap.elements_empty.
    split; [auto|].
    split; [|easy].
    intros ? ? find.
    now rewrite FMap.find_empty in find.
  - auto.
  - cbn -[Nat.ltb] in receive_some.
    destruct msg as [msg|]; cbn -[Nat.ltb] in *; [|congruence].
    destruct msg.
    + (* signup *)
      destruct (_ <? _)%nat eqn:intime in receive_some; cbn -[Nat.ltb] in *; [congruence|].
      apply Nat.ltb_ge in intime.
      destruct (FMap.find _ _) in receive_some; cbn in *; [|congruence].
      destruct (FMap.find _ _) eqn:new in receive_some; cbn in *; [congruence|].
      destruct (_ =? _)%Z in receive_some; cbn in *; [|congruence].
      destruct (_ <? _)%Z eqn:lt in receive_some; cbn in *; [|congruence].
      destruct (verify_secret_key_proof _ _ _) eqn:verify_zkp in receive_some;
        cbn in *; [|congruence].
      inversion_clear receive_some.
      cbn.
      split; [lia|].
      split; [tauto|].
      split.
      { rewrite app_length, FMap.size_add_new by auto; cbn; lia. }
      apply Z.ltb_lt in lt.
      rewrite app_length in *.
      cbn.
      fold (has_tallied prev_inc_calls).
      fold (signups prev_inc_calls).
      rewrite app_length, map_app; cbn.
      split; [destruct_and_split; congruence|].
      split; [lia|].
      intros [signup_assum msg_assum] order_assum num_signups_assum.
      destruct IH as [reg_lt [cur_lt [_ [pks_signups [_ IH]]]]].
      unshelve epose proof (IH _ _ _) as IH.
      * auto.
      * rewrite seq_app in order_assum.
        rewrite zip_app in order_assum by (now rewrite seq_length).
        apply All_app in order_assum.
        tauto.
      * intros.
        lia.
      * split.
        {
          destruct IH as [perm _].
          cbn.
          rewrite FMap.elements_add by auto.
          cbn.
          rewrite seq_app.
          cbn.
          perm_simplify.
        }
        split; cycle 1.
        {
          split; [easy|].
          intros tallied.
          specialize (cur_lt ltac:(lia)).
          congruence.
        }
        intros addr inf find_add.
        destruct (address_eqb_spec addr (ctx_from ctx)) as [->|].
        -- rewrite (FMap.find_add (ctx_from ctx)) in find_add.
           inversion_clear find_add.
           cbn.
           unfold make_signup_msg in signup_assum.
           rewrite nth_error_snoc.
           rewrite seq_app, zip_app in order_assum by (now rewrite seq_length).
           apply All_app in order_assum.
           cbn in order_assum.
           destruct order_assum as [_ []].
           split; [lia|].
           rewrite pks_signups, map_length.
           split; [symmetry; tauto|].
           split; [congruence|].
           left; easy.
        -- rewrite FMap.find_add_ne in find_add by auto.
           destruct IH as [_ [IH _]].
           specialize (IH _ _ find_add).
           split; [lia|].
           now rewrite nth_error_app1 by lia.
    + (* commit_to_vote *)
      destruct (finish_commit_by _); cbn -[Nat.ltb] in *; [|congruence].
      destruct (_ <? _); cbn in *; [congruence|].
      destruct (FMap.find _ _) eqn:found; cbn in *; [|congruence].
      inversion_clear receive_some; cbn.
      split; [lia|].
      split; [tauto|].
      split.
      { rewrite FMap.size_add_existing by congruence; tauto. }
      split; [tauto|].
      split; [tauto|].
      intros [_ msg_assum] order_assum num_signups_assum.
      destruct IH as [_ [_ [len_pks [_ [_ IH]]]]].
      specialize (IH msg_assum order_assum num_signups_assum).
      setoid_rewrite (FMap.keys_already _ _ _ _ found).
      split.
      {
        destruct IH as [perm _].
        rewrite len_pks in *.
        apply Permutation_modify with (vold := v); auto.
      }

      split; try tauto.
      intros addr inf find_add.
      destruct IH as [_ [IH _]].
      destruct (address_eqb_spec addr (ctx_from ctx)) as [->|].
      * rewrite FMap.find_add in find_add.
        inversion_clear find_add; cbn.
        auto.
      * rewrite FMap.find_add_ne in find_add by auto.
        auto.
    + (* submit_vote *)
      destruct (_ <? _); cbn -[Nat.ltb] in *; [congruence|].
      destruct (FMap.find _ _) eqn:found; cbn in *; [|congruence].
      destruct (if finish_commit_by _ then _ else _); cbn in *; [|congruence].
      destruct (verify_secret_vote_proof _ _ _ _); cbn in *; [|congruence].
      inversion_clear receive_some; cbn.
      split; [lia|].
      split; [tauto|].
      rewrite FMap.size_add_existing by congruence.
      split; [tauto|].
      split; [tauto|].
      split; [tauto|].
      intros [vote_assum msg_assum] order_assum num_signups_assum.
      destruct IH as [_ [_ [len_pks [_ [_ IH]]]]].
      specialize (IH msg_assum order_assum num_signups_assum).
      setoid_rewrite (FMap.keys_already _ _ _ _ found).
      split.
      {
        destruct IH as [perm _].
        rewrite len_pks in *.
        apply Permutation_modify with (vold := v0); auto.
      }
      split; [|tauto].
      intros addr inf find_add.
      destruct IH as [_ [IH _]].
      destruct (address_eqb_spec addr (ctx_from ctx)) as [->|].
      * rewrite FMap.find_add in find_add.
        inversion_clear find_add; cbn.
        specialize (IH _ _ found).
        repeat split; try tauto.
        right.
        unfold make_vote_msg in *.
        inversion vote_assum.
        destruct_hyps.
        replace (svi_index (parties (ctx_from ctx))) with (voter_index v0) by congruence.
        easy.
      * rewrite FMap.find_add_ne in find_add by auto.
        auto.
    + (* tally_votes *)
      destruct (_ <? _) eqn:intime; cbn in *; [congruence|].
      destruct (result prev_state); cbn in *; [congruence|].
      destruct (existsb _ _) eqn:all_voted; cbn in *; [congruence|].
      destruct (bruteforce_tally _) eqn:bruteforce; cbn -[Nat.ltb] in *; [|congruence].
      inversion_clear receive_some; cbn.
      apply Nat.ltb_ge in intime.
      split; [lia|].
      split; [intros; lia|].
      split; [tauto|].
      split; [tauto|].
      split; [tauto|].
      intros [_ msg_assum] order_assum num_signups_assum.
      split; [tauto|].
      split; [tauto|].
      split; [easy|].
      intros _.
      apply f_equal.
      destruct IH as [finish_before_vote [_ [len_pks [pks_signups [party_count IH]]]]].
      specialize (IH msg_assum order_assum num_signups_assum).
      destruct IH as [perm [addrs _]].
      unfold FMap.values in bruteforce.
      rewrite map_map in bruteforce.
      rewrite (map_ext_in _ (fun '(_, v) => public_vote v)) in bruteforce
        by (now intros []).
      rewrite (bruteforce_tally_correct
                    (FMap.elements (registered_voters prev_state))
                    (fun '(_, v) => voter_index v)
                    (fun '(addr, _) => svi_sk (parties addr))
                    (public_keys prev_state)
                    (fun kvp => svi_sv (parties (fst kvp)))
                    (fun '(_, v) => public_vote v)) in bruteforce.
      * inversion bruteforce.
        unfold FMap.keys.
        now rewrite sumnat_map.
      * now rewrite FMap.length_elements, <- len_pks.
      * now rewrite FMap.length_elements, <- len_pks.
      * auto.
      * intros [k v] kvpin.
        apply FMap.In_elements in kvpin.
        specialize (addrs _ _ kvpin).
        tauto.
      * intros [k v] kvpin.
        rewrite existsb_forallb in all_voted.
        apply Bool.negb_false_iff in all_voted.
        rewrite forallb_forall in all_voted.
        unshelve epose proof (all_voted v _) as all_voted.
        {
          apply in_map_iff.
          exists (k, v).
          tauto.
        }
        apply Bool.negb_true_iff in all_voted.
        destruct (elmeqb_spec (public_vote v) zero); [congruence|].
        apply FMap.In_elements in kvpin.
        specialize (addrs _ _ kvpin).
        cbn.
        destruct addrs as [_ [_ [_ []]]]; [easy|].
        fold (signups prev_inc_calls) (SignupOrderAssumption pks parties prev_inc_calls) in *.
        rewrite pks_signups.
        specialize (num_signups_assum ltac:(lia)).
        now rewrite (all_signups pks parties) by auto.
  - [CallFacts]: exact (fun _ ctx _ => ctx_from ctx <> ctx_contract_address ctx).
    subst CallFacts; cbn in *; congruence.
  - auto.
  - [DeployFacts]: exact (fun _ _ => True).
    unset_all; subst; cbn in *.
    destruct_chain_step; auto.
    + destruct valid_header; auto.
    + destruct_action_eval; auto.
      intros.
      pose proof (no_outgoing _ _ from_reachable H0).
      unfold outgoing_acts in H2.
      rewrite queue_prev in H2.
      cbn in H2.
      destruct (address_eqb_spec (act_from act) to_addr); cbn in *; try congruence.
      subst act; cbn in *; congruence.
Qed.

Theorem boardroom_voting_correct
        (bstate : ChainState)
        (caddr : Address)
        (trace : ChainTrace empty_state bstate)
        (* list of all public keys, in the order of signups *)
        (pks : list A)
        (* function mapping a party to information about him *)
        (parties : Address -> SecretVoterInfo) :
    env_contracts bstate caddr = Some (boardroom_voting : WeakContract) ->
    exists (cstate : State)
           (depinfo : DeploymentInfo Setup)
           (inc_calls : list (ContractCallInfo Msg)),
      deployment_info Setup trace caddr = Some depinfo /\
      contract_state bstate caddr = Some cstate /\
      incoming_calls Msg trace caddr = Some inc_calls /\

      (* assuming that the message sent were created with the
          functions provided by this smart contract *)
      MsgAssumption pks parties inc_calls ->

      (* ..and that people signed up in the order given by 'index'
          and 'pks' *)
      SignupOrderAssumption pks parties inc_calls ->

      (* ..and that the correct number of people register *)
      (finish_registration_by (setup cstate) < Blockchain.current_slot bstate ->
       length pks = length (signups inc_calls)) ->

      (* then if we have not tallied yet, the result is none *)
      ((has_tallied inc_calls = false -> result cstate = None) /\
       (* or if we have tallied yet, the result is correct *)
       (has_tallied inc_calls = true ->
        result cstate = Some (sumnat (fun party => if svi_sv (parties party) then 1 else 0)%nat
                                     (FMap.keys (registered_voters cstate))))).
Proof.
  intros deployed.
  destruct (boardroom_voting_correct_strong bstate caddr trace parties pks deployed)
    as [cstate [depinfo [inc_calls P]]].
  exists cstate, depinfo, inc_calls.
  tauto.
Qed.

End Theories.

End BoardroomVoting.

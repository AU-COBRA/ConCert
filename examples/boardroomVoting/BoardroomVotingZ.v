From Coq Require Import List.
From Coq Require Import ZArith.
From Coq Require Import Znumtheory.
From Coq Require Import Permutation.
From Coq Require Import Lia.
From ConCert.Utils Require Import Extras.
From ConCert.Utils Require Import RecordUpdate.
From ConCert.Execution Require Import Blockchain.
From ConCert.Execution Require Import Containers.
From ConCert.Execution Require Import Monad.
From ConCert.Execution Require Import ResultMonad.
From ConCert.Execution Require Import Serializable.
From ConCert.Execution Require Import ContractMonads.
From ConCert.Execution Require Import ContractCommon. Import AddressMap.
From ConCert.Examples.BoardroomVoting Require Import Egcd.
From ConCert.Examples.BoardroomVoting Require Import Euler.

Import ListNotations.



Module Type BoardroomParams.
  Parameter H : list positive -> positive.
  Parameter prime : Z.
  Parameter generator : Z.
  Parameter Base : ChainBase.
End BoardroomParams.

Module BoardroomVoting (Params : BoardroomParams).
  Import Params.
  #[export]
  Existing Instance Base.

  Definition A := Z.
  Definition elmeqb (a b : A) := a mod prime =? b mod prime.
  Definition mod_inv (a : Z) (p : Z) : Z :=
    let x := (egcd a p) in
    (fst x) mod p.

  Definition amount_eqb (a b : Amount) : bool := Z.eqb a b.


  Fixpoint mod_pow_pos_aux (a : Z) (x : positive) (m : Z) (r : Z) : Z :=
    match x with
    | x~0%positive => mod_pow_pos_aux (a * a mod m) x m r
    | x~1%positive => mod_pow_pos_aux (a * a mod m) x m (r * a mod m)
    | _ => r * a mod m
    end.

  Definition mod_pow_pos (a : Z) (x : positive) (m : Z) : Z :=
    mod_pow_pos_aux a x m 1.

  Definition mod_pow (a x p : Z) : Z :=
    match x with
    | Z0 => a ^ 0 mod p
    | Zpos x => mod_pow_pos a x p
    | Zneg x => mod_inv (mod_pow_pos a x p) p
    end.

  Definition add_p a b := (a + b) mod prime.
  Definition mul_p a b := (a * b) mod prime.
  Definition opp_p a := prime - a.
  Definition inv_p a := mod_inv a prime.
  Definition pow_p a e := mod_pow a e prime.
  Definition order := prime.
  Declare Scope broom.
  Declare Scope broom_scope.
  Delimit Scope broom_scope with broom.

  Module BoardroomMathNotations.

    Infix "=?" := elmeqb (at level 70) : broom.
    Notation "0" := 0%Z : broom.
    Notation "1" := 1%Z : broom.
    Infix "+" := add_p : broom.
    Infix "*" := mul_p : broom.
    Infix "^" := pow_p : broom.
  End BoardroomMathNotations.

  Import BoardroomMathNotations.
  Local Open Scope broom.


  (* Allow us to automatically derive Serializable instances *)
  Set Nonrecursive Elimination Schemes.
  Set Primitive Projections.

  Record Setup :=
    build_setup {
      eligible_voters : AddrMap unit;
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
      registered_voters : AddrMap VoterInfo;
      public_keys : list A;
      setup : Setup;
      tally : option nat;
    }.

  Definition Error : Type := nat.
  Definition default_error : Error := 1%nat.

  (* w, a1, b1, a2, b2, d1, d2 *)
  Definition VoteProof := (Z * A * A * A * A * Z * Z * Z * Z)%type.

  Inductive Msg :=
  | signup (pk : A) (proof : A * Z)
  | commit_to_vote (hash : positive)
  | submit_vote (v : A) (proof : VoteProof)
  | tally_votes.

  (* begin hide *)
  MetaCoq Run (make_setters VoterInfo).
  MetaCoq Run (make_setters State).
  (* end hide *)

  Section Serialization.
    Global Instance Setup_serializable : Serializable Setup :=
      Derive Serializable Setup_rect<build_setup>.

    Global Instance VoterInfo_serializable : Serializable VoterInfo :=
      Derive Serializable VoterInfo_rect<build_voter_info>.

    Global Instance State_serializable : Serializable State :=
      Derive Serializable State_rect<build_state>.

    Global Instance Msg_serializable : Serializable Msg :=
      Derive Serializable Msg_rect<signup, commit_to_vote, submit_vote, tally_votes>.
  End Serialization.

  Definition encodeA : A -> positive := countable.encode.
  Definition encodeNat : nat -> positive := countable.encode.


  Definition hash_sk_data (gv pk : A) (i : nat) : positive :=
    H [encodeA (generator : A); encodeA gv; encodeA pk; encodeNat i].

  Definition compute_public_key (sk : Z) : A :=
    pow_p generator sk.

  (* This follows the original open vote protocol paper. It is a schnorr signature
      with the fiat-shamir heuristic applied. *)
  Definition secret_key_proof (sk : Z) (v : Z) (i : nat) : A * Z :=
    let gv : A := pow_p generator v in
    let pk := compute_public_key sk in
    let z := Zpos (hash_sk_data gv pk i) in
    let r := (v - sk * z)%Z in
    (gv, r).

  Definition verify_secret_key_proof (pk : A) (i : nat) (proof : A * Z) : bool :=
    let (gv, r) := proof in
    let z := Zpos (hash_sk_data gv pk i) in
    elmeqb gv ((pow_p generator r) * (pow_p pk z)).

  Definition hash_sv_data (i : nat) (pk rk a1 b1 a2 b2 : A) : positive :=
    H (encodeNat i :: map encodeA [pk; rk; a1; b1; a2; b2]).
  Definition compute_public_vote (rk : A) (sk : Z) (sv : bool) : A :=
    pow_p rk sk * if sv then generator else 1.

  Definition secret_vote_proof (sk : Z) (rk : A) (sv : bool) (i : nat) (w r d : Z) : VoteProof :=
    let pk : A := compute_public_key sk in
    let pv : A := compute_public_vote rk sk sv in
    if sv then
      let a1 : A := pow_p generator r * pow_p pk d in
      let b1 : A := pow_p rk r * pow_p pv d in
      let a2 : A := pow_p generator w in
      let b2 : A := pow_p rk w in
      let c := Zpos (hash_sv_data i pk rk a1 b1 a2 b2) in
      let d2 := c - d in
      let r2 := w - sk*d2 in
      (w, a1, b1, a2, b2, d, d2, r, r2)
    else
      let a1 := pow_p generator w in
      let b1 := pow_p rk w in
      let a2 := pow_p generator r * pow_p pk d in
      let b2 := pow_p rk r * (pow_p (pv * inv_p generator) d) in
      let c := Zpos (hash_sv_data i pk rk a1 b1 a2 b2) in
      let d1 := c - d in
      let r1 := w - sk*d1 in
      (w, a1, b1, a2, b2, d1, d, r1, r).

  Local Open Scope bool.
  Definition verify_secret_vote_proof (pk rk pv : A) (i : nat) (proof : VoteProof) : bool :=
    let '(w, a1, b1, a2, b2, d1, d2, r1, r2) := proof in
    let c := hash_sv_data i pk rk a1 b1 a2 b2 in
    (Zpos c =? d1 + d2)%Z &&
    (a1 =? pow_p generator r1 * pow_p pk d1)%broom &&
    (b1 =? pow_p rk r1 * pow_p pv d1)%broom &&
    (a2 =? pow_p generator r2 * pow_p pk d2)%broom &&
    (b2 =? pow_p rk r2 * pow_p (pv * inv_p generator) d2)%broom.

  Definition make_signup_msg (sk : Z) (v : Z) (i : nat) : Msg :=
    signup (compute_public_key sk) (secret_key_proof sk v i).

  Definition reconstructed_key (pks : list A) (n : nat) : A :=
    let lprod := prod (firstn n pks) in
    let rprod := inv_p (prod (skipn (S n) pks)) in
    lprod * rprod.

  Definition make_commit_msg (pks : list A) (my_index : nat) (sk : Z) (sv : bool) : Msg :=
    let pv := compute_public_vote (reconstructed_key pks my_index) sk sv in
    commit_to_vote (H [encodeA pv]).

  Definition make_vote_msg (pks : list A) (my_index : nat) (sk : Z) (sv : bool) (w r d : Z) : Msg :=
    let rk := reconstructed_key pks my_index in
    submit_vote (compute_public_vote rk sk sv)
                (secret_vote_proof sk rk sv my_index w r d).

  Definition assert_true_init (check : bool) : ContractIniter Setup Error unit :=
    @lift _ (fun T => result T Error) _ _ (if check then Ok tt else Err default_error).
  Definition assert_true (check : bool) : ContractReceiver State Msg Error unit :=
    @lift _ (fun T => result T Error) _ _ (if check then Ok tt else Err default_error).
  Definition assert_false (check : bool) : ContractReceiver State Msg Error unit :=
    @lift _ (fun T => result T Error) _ _ (if check then Err default_error else Ok tt).
  Definition assert_some {A : Type} (check : option A) : ContractReceiver State Msg Error unit :=
    @lift _ (fun T => result T Error) _ _ (if check then Ok tt else Err default_error).
  Definition assert_none {A : Type} (check : option A) : ContractReceiver State Msg Error unit :=
    @lift _ (fun T => result T Error) _ _ (if check then Err default_error else Ok tt).

  Definition ContractIniterSetupState := ContractIniter Setup Error State.

  Definition init : ContractIniterSetupState :=
    do owner <- lift caller_addr;
    do setup <- deployment_setup;
    do assert_true_init (finish_registration_by setup <? finish_vote_by setup)%nat;
    accept_deployment
      {| owner := owner;
        registered_voters := AddressMap.empty;
        public_keys := [];
        setup := setup;
        tally := None; |}.

  Definition ContractReceiverStateMsgState := ContractReceiver State Msg Error State.
  Definition twoZ : Z := 2.

  Definition handle_signup pk prf state caller cur_slot : ContractReceiverStateMsgState :=
    do assert_false (finish_registration_by (setup state) <? cur_slot)%nat;
    do assert_some (AddressMap.find caller (eligible_voters (setup state)));
    do assert_none (AddressMap.find caller (registered_voters state));
    do amt <- lift call_amount;
    do assert_true (amount_eqb amt (registration_deposit (setup state)))%Z;
    do assert_true (Z.of_nat (length (public_keys state)) <? order - 2);
    let index := length (public_keys state) in
    do assert_true (verify_secret_key_proof pk index prf);
    let inf := {| voter_index := index;
                  vote_hash := 1;
                  public_vote := 0; |} in
    let new_state := {| owner := state.(owner);
                        registered_voters := AddressMap.add caller inf state.(registered_voters);
                        public_keys := state.(public_keys) ++ [pk];
                        setup := state.(setup);
                        tally := state.(tally);
                    |} in
    accept_call new_state.

  Definition handle_commit_to_vote hash_ state caller cur_slot : ContractReceiverStateMsgState :=
    do commit_by <- lift (result_of_option (finish_commit_by (setup state)) default_error);
    do assert_false (commit_by <? cur_slot)%nat;
    do inf <- lift (result_of_option (AddressMap.find caller (registered_voters state)) default_error);
    let inf := inf<|vote_hash := hash_|> in
    accept_call (state<|registered_voters ::= AddressMap.add caller inf|>).

  Definition handle_submit_vote v proof state caller cur_slot : ContractReceiverStateMsgState :=
    do assert_false (finish_vote_by (setup state) <? cur_slot)%nat;
    do inf <- lift (result_of_option (AddressMap.find caller (registered_voters state)) default_error);
    do @lift _ (fun T => result T Error) _ _ (if finish_commit_by (setup state) then
              if (H [encodeA v] =? vote_hash inf)%positive then Ok tt else Err default_error
            else
              Ok tt);
    do @lift _ (fun T => result T Error) _ _ (if verify_secret_vote_proof
                  (nth (voter_index inf) (public_keys state) 0)
                  (reconstructed_key (public_keys state) (voter_index inf))
                  v
                  (voter_index inf)
                  proof then Ok tt else Err default_error);
    let inf := inf<|public_vote := v|> in
    accept_call (state<|registered_voters ::= AddressMap.add caller inf|>).

  Fixpoint bruteforce_tally_aux
            (n : nat)
            (votes_product : A) : result nat Error :=
    if generator ^ (Z.of_nat n) =? votes_product then
      Ok n
    else
      match n with
      | 0 => Err default_error
      | S n => bruteforce_tally_aux n votes_product
      end%nat.

  Definition bruteforce_tally (votes : list A) : result nat Error :=
    bruteforce_tally_aux (length votes) (prod votes).

  Definition handle_tally_votes state cur_slot : ContractReceiverStateMsgState :=
    do assert_false (cur_slot <? finish_vote_by (setup state))%nat;
    do assert_none (tally state);
    let voters := AddressMap.values (registered_voters state) in
    do assert_false (existsb
                  (fun vi => if elmeqb (public_vote vi) 0 then true else false)
                  voters);
    let votes := map public_vote voters in
    do res <- @lift _ (fun T => result T Error) _ _ (bruteforce_tally votes);
    accept_call (state<|tally := Some res|>).

  Definition receive : ContractReceiverStateMsgState :=
    do state <- my_state;
    do caller <- lift caller_addr;
    do cur_slot <- lift current_slot;
    do msg <- call_msg default_error;
    match msg with
    | signup pk prf => handle_signup pk prf state caller cur_slot
    | commit_to_vote hash_ => handle_commit_to_vote hash_ state caller cur_slot
    | submit_vote v proof => handle_submit_vote v proof state caller cur_slot
    | tally_votes => handle_tally_votes state cur_slot
    end.

  Definition boardroom_voting : Contract Setup Msg State Error :=
    build_contract init receive.

  Section Theories.

    Record SecretVoterInfo :=
      build_secret_voter_info {
        svi_index : nat;
        (* Secret key *)
        svi_sk : Z;
        (* Chosen randomness for knowledge of secret key proof *)
        svi_sk_r : Z;
        (* Secret vote *)
        svi_sv : bool;
        (* Chosen random w for vote proof *)
        svi_sv_w : Z;
        (* Chosen random r for vote proof *)
        svi_sv_r : Z;
        (* Chosen random d for vote proof *)
        svi_sv_d : Z;
      }.

    (* begin hide *)
    MetaCoq Run (make_setters SecretVoterInfo).
    (* end hide *)

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
          m = make_vote_msg
                pks
                (svi_index party)
                (svi_sk party)
                (svi_sv party)
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

    Lemma Permutation_modify k vold vnew (m : AddrMap VoterInfo) :
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
        destruct H1; lia.
    Qed.

  End Theories.

End BoardroomVoting.

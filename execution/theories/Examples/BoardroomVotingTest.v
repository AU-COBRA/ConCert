From Bignums Require Import BigZ.
From Coq Require Import Cyclic31.
From Coq Require Import List.
From Coq Require Import Znumtheory.
Require Import BignumsSerializable.
Require Import Blockchain.
Require Import BoardroomMath.
Require Import BoardroomVoting.
Require Import BoundedN.
Require Import Containers.
Require Import Extras.
Require Import LocalBlockchain.
Require Import Monads.
Require Import Serializable.

Import ListNotations.

Local Open Scope bigZ.
Local Open Scope ffield.
(*
Definition modulus : bigZ := 1552518092300708935130918131258481755631334049434514313202351194902966239949102107258669453876591642442910007680288864229150803718918046342632727613031282983744380820890196288509170691316593175367469551763119843371637221007210577919.
Definition generator : bigZ := 2.
*)
Definition modulus : bigZ := 201697267445741585806196628073.
Definition generator : bigZ := 3.

Axiom modulus_prime : prime [modulus].
Instance axioms : BoardroomAxioms bigZ := BigZp.boardroom_axioms modulus modulus_prime.

Lemma generator_nonzero : generator !== 0.
Proof. discriminate. Qed.

Axiom generator_is_generator :
  forall z,
    z !== 0 ->
    exists! (e : Z), (0 <= e < order - 1)%Z /\ pow generator e == z.

Instance generator_instance : Generator axioms :=
  {| BoardroomMath.generator := generator;
     BoardroomMath.generator_nonzero := generator_nonzero;
     generator_generates := generator_is_generator; |}.

Instance id_scheme : @VoteProofScheme bigZ :=
  {| make_vote_proof l n z b := 0%Z;
     verify_vote l n a z := true; |}.

Definition num_parties : nat := 7.
Definition votes_for : nat := 4.

(* a pseudo-random generator for secret keys *)
Definition sk n := [pow ((BigZ.of_Z (Z.of_nat n) + 1234583932) * (modulus - 23241)) 159338231].

(* Make a list of secret keys, here starting at i=7 *)
Definition sks : list Z :=
  Eval native_compute in map sk (seq 7 num_parties).

(* Make a list of votes for each party *)
Definition svs : list bool :=
  Eval compute in map (fun _ => true)
                      (seq 0 votes_for)
                  ++ map (fun _ => false)
                         (seq 0 (num_parties - votes_for)).

(* Compute the public keys for each party *)
Definition pks : list bigZ :=
  Eval native_compute in map compute_public_key sks.

(* Compute the signup messages that would be sent by each party *)
Definition signups : list Msg :=
  Eval native_compute in map make_signup_msg sks.

(* Compute the submit_vote messages that would be sent by each party *)
(* Our functional correctness proof assumes that the votes were computed
   using the make_vote_msg function provided by the contract *)
Definition votes : list Msg :=
  Eval native_compute in map (fun '(i, sk, sv) => make_vote_msg pks i sk sv)
                             (zip (zip (seq 0 (length pks)) sks) svs).

Definition AddrSize := (2^128)%N.
Instance Base : ChainBase := LocalChainBase AddrSize.
Instance ChainBuilder : ChainBuilderType := LocalChainBuilderDepthFirst AddrSize.

Definition A a :=
  BoundedN.of_Z_const AddrSize a.

Local Open Scope nat.
Definition addrs : list Address.
Proof.
  let rec add_addr z n :=
    match n with
    | O => constr:(@nil Address)
    | S ?n => let tail := add_addr (z + 1)%Z n in
              constr:(cons (A z) tail)
    end in
  let num := eval compute in num_parties in
  let tm := add_addr 11%Z num in
  let tm := eval vm_compute in tm in
  exact tm.
Defined.

Definition deploy_setup :=
  {| eligible_voters := FMap.of_list (map (fun a => (a, tt)) addrs);
     finish_registration_by := 3;
     finish_commit_by := None;
     finish_vote_by := 5;
     registration_deposit := 0; |}.

Local Open Scope list.
Definition boardroom_example :=
  let chain : ChainBuilder := builder_initial in
  let creator : Address := A 10 in
  let add_block (chain : ChainBuilder) (acts : list Action) :=
      let next_header :=
          {| block_height := S (chain_height chain);
             block_slot := S (current_slot chain);
             block_finalized_height := finalized_height chain;
             block_creator := creator;
             block_reward := 50; |} in
      builder_add_block chain next_header acts in
  do chain <- add_block chain [];
  let dep := build_act creator (create_deployment 0 (boardroom_voting BigZ.to_Z) deploy_setup) in
  do chain <- add_block chain [dep];
  do caddr <- hd None (map Some (FMap.keys (lc_contracts (lcb_lc chain))));
  let send addr m := build_act addr (act_call caddr 0 (serialize m)) in
  let calls := map (fun '(addr, m) => send addr m) (zip addrs signups) in
  do chain <- add_block chain calls;
  let votes := map (fun '(addr, m) => send addr m) (zip addrs votes) in
  do chain <- add_block chain votes;
  let tally := build_act creator (act_call caddr 0 (serialize tally_votes)) in
  do chain <- add_block chain [tally];
  do state <- @contract_state _ (@State _ bigZ) _ (lcb_lc chain) caddr;
  result state.

Check (@eq_refl (option nat) (Some votes_for)) <: boardroom_example = Some votes_for.

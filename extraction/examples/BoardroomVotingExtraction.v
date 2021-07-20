(** * Extraction of a counter contract with refinement types to Liquidity *)

(** The contract uses refinement types to specify some functional correctness properties *)

From Coq Require Import PeanoNat ZArith.

From ConCert.Extraction Require Import LPretty LiquidityExtract Common.
From ConCert.Execution Require Import Blockchain Common LocalBlockchain.

From Coq Require Import List String.
Local Open Scope string_scope.

From MetaCoq.Template Require Import All.

Import ListNotations.
Import MonadNotation.
Import AddressMap.

Open Scope Z.

Definition PREFIX := "".

From ConCert.Execution.Examples Require Import BoardroomVotingZ.

(* In this example we just use xor for the hash function, which is
   obviously not cryptographically secure. *)
Definition modulus : Z := 201697267445741585806196628073.
Definition four := 4%nat.
Definition seven := 7%nat.
Definition _1234583932 := 1234583932.
Definition _23241 := 23241.
Definition _159338231 := 159338231.
Definition oneN : N := 1%N.
Definition Z3 : Z := 3.
Definition generator : Z := Z3.

Definition hash_func (l : list positive) : positive :=
  N.succ_pos (fold_left (fun a p => N.lxor (Npos p) a) l oneN).

  (* Instance Base : ChainBase := LocalChainBase AddrSize. *)
Definition AddrSize := (2^128)%N.
Instance Base : ChainBase := LocalBlockchain.LocalChainBase AddrSize.

Module Params <: BoardroomParams.
  Definition H : list positive -> positive := hash_func.
  Definition Base := Base .
  Definition prime := modulus.
  Definition generator := generator.
End Params.  
Module BV := BoardroomVoting Params. Import BV.

(* Compute the signup messages that would be sent by each party.
   We just use the public key as the chosen randomness here. *)
Definition _3 := 3%nat.
Definition _5 := 5.
Definition _11 := 11.

Definition num_parties : nat := seven.
Definition votes_for : nat := four.

(* a pseudo-random generator for secret keys *)
Definition sk n := (Z.of_nat n + _1234583932) * (modulus - _23241)^_159338231.

(* Make a list of secret keys, here starting at i=7 *)
Definition sks : list Z := map sk (seq seven num_parties).

(* Make a list of votes for each party *)
Definition svs : list bool :=
  Eval compute in map (fun _ => true)
                      (seq 0 votes_for)
                  ++ map (fun _ => false)
                         (seq 0 (num_parties - votes_for)).

(* Compute the public keys for each party *)
(* 
Time Definition pks : list Z :=
  Eval vm_compute in map compute_public_key sks.

Definition rks : list Z :=
  Eval vm_compute in map (reconstructed_key pks) (seq 0 (length pks)).

Time Definition signups : list Msg :=
  Eval vm_compute in map (fun '(sk, pk, i) => make_signup_msg sk _5 i)
                             (Extras.zip (zip sks pks) (seq 0 (length sks))).

(* Compute the submit_vote messages that would be sent by each party *)
(* Our functional correctness proof assumes that the votes were computed
   using the make_vote_msg function provided by the contract.
   In this example we just use the secret key as the random parameters. *)
Definition votes : list Msg :=
  Eval vm_compute in map (fun '(i, sk, sv, rk) => make_vote_msg pks i sk sv sk sk sk)
                             (zip (zip (zip (seq 0 (length pks)) sks) svs) rks).

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
  let tm := add_addr _11%Z num in
  let tm := eval vm_compute in tm in
  exact tm.
Defined.

Definition voters_map : AddrMap unit := AddressMap.of_list (map (fun a => (a, tt)) addrs).

Definition five := 5%nat.

Definition deploy_setup :=
  {| eligible_voters := voters_map;
     finish_registration_by := _3;
     finish_commit_by := None;
     finish_vote_by := five;
     registration_deposit := 0; |}. *)

(* Get string representation of modulus, and remap it. This way we avoid having the extraction compute the number. *)
Definition modulus_ := StringExtra.string_of_Z modulus.

Require Import ContractMonads.

Definition init_ctx := (Chain × ContractCallContext).

Definition init_wrapper (cctx : init_ctx) := (run_contract_initer BV.init) cctx.1 cctx.2.

Notation msg := (Chain × ContractCallContext × option BV.Msg).

Definition receive_wrapper (msg : msg)
                           (st : BV.State) : option (list ActionBody * BV.State):= 
                           (* None. *)
  match (run_contract_receiver BV.receive) msg.1 msg.2.1 st msg.2.2 with
  | Some (st, acts) => Some (acts, st)
  | None => None
  end.

Definition dummy_init : init_ctx -> BV.Setup -> option BV.State := fun _ _ => None .

Definition dummy_receive : msg -> BV.State -> option (list ActionBody × BV.State) := 
  fun _ _  => 
    let x := add_p 0 _5 in
    None.

Definition BV_MODULE : LiquidityMod msg init_ctx BV.Setup BV.State ActionBody :=
  {| (* a name for the definition with the extracted code *)
    lmd_module_name := "liquidity_boardroomvoting" ;

    (* definitions of operations on pairs and ints *)
    lmd_prelude := LiquidityPrelude;

    (* initial storage *)
    lmd_init := init_wrapper;

    (* no extra operations in [init] are required *)
    lmd_init_prelude := "" ;

    (* the main functionality *)
    lmd_receive := receive_wrapper;

    (* code for the entry point *)
    lmd_entry_point := printWrapper (PREFIX ++ "receive_wrapper") ++ nl
                      ++ printMain |}.

(** We run the extraction procedure inside the [TemplateMonad].
    It uses the certified erasure from [MetaCoq] and the certified deboxing procedure
    that removes application of boxes to constants and constructors. *)
(* Require Import RecordSet. *)

Definition inline_boardroom_params : list kername :=
  [
      <%% Params.H %%>
    ; <%% Params.generator %%>
  ].


Definition inline_contract_monad_projection : list kername := 
  [
      <%% @chain_height %%>
    ; <%% @current_slot %%>
    ; <%% @finalized_height %%>
    ; <%% @caller_addr %%>
    ; <%% @my_addr %%>
    ; <%% @my_balance %%>
    ; <%% @call_amount %%>
    ; <%% @deployment_setup %%>
    ; <%% @reject_deployment %%>
    ; <%% @accept_deployment %%>
    ; <%% @call_msg %%>
    ; <%% @my_state %%>
    ; <%% @queue %%>
    ; <%% @reject_call %%>
    ; <%% @accept_call %%>
    ; <%% @build_contract %%>
  ].


Definition to_inline : list kername := 
     inline_contract_monad_projection
  ++ inline_boardroom_params
  ++ [
    <%% Monads.Monad_option %%>
  (* ; <%% @Monads.MonadTrans %%> *)
  
  ; <%% ContractIniterSetupState %%>
  ; <%% ContractReceiverStateMsgState %%>
  ; <%% @contract_initer_monad %%>
  ; <%% @run_contract_initer %%>
  ; <%% @contract_receiver_monad %%>
  ; <%% @contract_reader_to_contract_initer %%>
  ; <%% @option_to_contract_initer %%>
  ; <%% @contract_reader_to_receiver %%>
  ; <%% @option_to_contract_receiver %%>
  
  ; <%% @ContractReceiver %%>
  ; <%% @ContractIniter %%>
  (* Dont work *)
  (* ; <%% @ContractReader %%> *)
  
  ; <%% @Monads.bind %%>
  ; <%% @Monads.ret %%>
  ; <%% @Monads.lift %%>
  ; <%% bool_rect %%>
  ; <%% bool_rec %%>
  ; <%% option_map %%>
  ; <%% @Extras.with_default %%>

  ; <%% @BV.setter_from_getter_State_owner %%>
  ; <%% @BV.setter_from_getter_State_registered_voters %%>
  ; <%% @BV.setter_from_getter_State_public_keys %%>
  ; <%% @BV.setter_from_getter_State_setup %%>
  ; <%% @BV.setter_from_getter_State_tally %%>

  ; <%% @BV.setter_from_getter_VoterInfo_voter_index %%>
  ; <%% @BV.setter_from_getter_VoterInfo_vote_hash %%>
  ; <%% @BV.setter_from_getter_VoterInfo_public_vote %%>

  ; <%% @BV.set_State_owner %%>
  ; <%% @BV.set_State_registered_voters %%>
  ; <%% @BV.set_State_public_keys %%>
  ; <%% @BV.set_State_setup %%>
  ; <%% @BV.set_State_tally %%>

  ; <%% @BV.set_VoterInfo_voter_index %%>
  ; <%% @BV.set_VoterInfo_vote_hash %%>
  ; <%% @BV.set_VoterInfo_public_vote %%>

  (* ; <%% @countable.encode %%> *)
  ].

(* Definition asd := (BoardroomMath.add 1 2).

Time MetaCoq Quote Recursively Definition ex1 := asd.
Check ex1.
Definition r1 := Eval vm_compute in (liquidity_extract_single TT_remap TT_rename true BV_MODULE.(lmd_prelude) "harness?" ex1).
Print r1. *)
(* r1 = 
inr
  "Erased environment is not expanded enough for dearging to be provably correct"
  : string + string
*)

(* Time MetaCoq Run ('(env, init_nm, receive_nm) <- quote_and_preprocess to_inline BV_MODULE ;;
                  tmDefinition "bv_env" env ;;
                  tmDefinition "bv_init_nm" init_nm ;;
                  tmDefinition "bv_receive_nm" receive_nm). *)


(** A translation table for definitions we want to remap. The corresponding top-level definitions will be *ignored* *)
Definition TT_remap : list (kername * string) :=
  (* TT_remap_default ++  *)
  [
    remap <%% Amount %%> "tez"
  ; remap <%% positive %%> "nat"
  ; remap <%% Z %%> "int"
  ; remap <%% Z.of_nat %%> "int"
  ; remap <%% Z.add %%> "addInt"
  ; remap <%% Z.sub %%> "subInt"
  ; remap <%% Z.leb %%> "leInt"
  ; remap <%% Z.ltb %%> "ltInt"
  ; remap <%% Z.add %%> "addInt"
  ; remap <%% Z.eqb %%> "eqInt"
  ; remap <%% Z.gtb %%> "gtbInt"
  ; remap <%% Nat.ltb %%> "ltbNat"
  ; remap <%% Z.modulo %%> "modInt"
  ; remap <%% Z.mul %%> "mulInt"
  (* ; remap <%% Z.pow %%> "powInt" *)
  ; remap <%% N.lxor %%> "lxorNat"
  ; remap <%% N.succ_pos %%> "(addNat 1)"
  ; remap <%% mod_pow %%> "mod_pow"
  ; remap <%% Egcd.egcd %%> "egcd"
  (* ; remap <%% List.nth %%> "List.nth" *)
  (* ; remap <%% List.firstn %%> "List.firstn" *)
  (* ; remap <%% List.skipn %%> "List.skipn" *)

  ; remap <%% oneN %%> "1"
  ; remap <%% four %%> "4"
  ; remap <%% seven %%> "7"
  ; remap <%% _1234583932 %%> "1234583932"
  ; remap <%% _23241 %%> "23241"
  ; remap <%% _159338231 %%> "159338231"
  ; remap <%% _5 %%> "5"
  ; remap <%% _3 %%> "3"
  ; remap <%% Z3 %%> "3"
  ; remap <%% _11 %%> "11"
  (* ; remap <%% five %%> "5" *)
  ; remap <%% @ContractCallContext %%> "(address * (address * int))"
  ; remap <%% @Chain %%> "(address * (address * address))" (* chain_height, current_slot, finalized_height *)
  ; remap <%% @chain_height %%> "fst" (* small hack, but valid since ContractCallContext is mapped to a tuple *)
  ; remap <%% @current_slot %%> "(fun c -> fst (snd c)" (* small hack, but valid since Chain is mapped to a tuple *)
  ; remap <%% @finalized_height %%> "(fun c -> snd (snd c)" (* small hack, but valid since Chain is mapped to a tuple *)
  ; remap <%% @ctx_from %%> "fst" (* small hack, but valid since ContractCallContext is mapped to a tuple *)
  ; remap <%% @AddressMap.AddrMap %%> "addrMap"
  ; remap <%% @AddressMap.add %%> "Map.add"
  ; remap <%% @AddressMap.find %%> "Map.find"
  ; remap <%% @AddressMap.values %%> "Map.to_list"
  ; remap <%% @AddressMap.empty %%> "(Map [])"

  (* ; remap <%% BV.verify_secret_vote_proof %%> "verify_secret_vote_proof" *)
  (* ; remap <%% @BV.make_signup_msg %%> "make_signup_msg" *)
  (* ; remap <%% @BV.make_commit_msg %%> "make_commit_msg" *)
  (* ; remap <%% @BV.make_vote_msg %%> "make_vote_msg" *)
  (* ; remap <%% @BV.secret_vote_proof %%> "secret_vote_proof" *)
  (* ; remap <%% @BV.secret_key_proof %%> "secret_key_proof" *)
  (* ; remap <%% @BV.hash_sk_data %%> "hash_sk_data" *)
  (* ; remap <%% @BV.hash_sv_data %%> "hash_sv_data" *)

  (* ; remap <%% @BV.handle_signup %%> "handle_signup" *)
  (* ; remap <%% @BV.handle_commit_to_vote %%> "handle_commit_to_vote" *)
  (* ; remap <%% @BV.handle_submit_vote %%> "handle_submit_vote" *)
  (* ; remap <%% @BV.handle_tally_votes %%> "handle_tally_votes" *)


  ; remap <%% modulus %%> modulus_
  ; remap <%% BV.encodeA %%> "nat"
  ; remap <%% BV.encodeNat %%> "nat"
  

  ; remap <%% @List.fold_left %%> "List.fold"
  ; remap <%% @List.map %%> "List.map"
  ; remap <%% @List.find %%> "List.find"
  ; remap <%% @List.length %%> "List.length"
  ; remap <%% @List.app %%> "List.append"
  ; remap <%% @Serializable.serialize %%> "TODO_serialize"
  ; remap <%% @Serializable.deserialize %%> "TODO_deserialize"
  ].
(** A translation table of constructors and some constants. The corresponding definitions will be extracted and renamed. *)
Definition TT_rename : list (string * string):=
  [ ("Some", "Some")
  ; ("None", "None")
  ; ("Zpos" ,"int")
  ; ("Npos" ,"(fun (n:nat) -> n)")
  ; ("Zneg" ,"-")
  ; ("Z0" ,"0")
  ; ("N0" ,"0")
  ; ("xH" ,"0")
  ; ("1" ,"1")
  ; ("nil", "[]")
  ; ("true", "true")
  ; ("false", "false")
  ; (string_of_kername <%% BV.State %%>, "State")  (* we add [storage] so it is printed without the prefix *) 
  ; ("tt", "()")
  ].

(* Time MetaCoq Run (
  t <- liquidity_prepare_extraction PREFIX TT_remap TT_rename to_inline BV_MODULE bv_env bv_init_nm bv_receive_nm ;;
  tmDefinition BV_MODULE.(lmd_module_name) t
  ).

Print liquidity_boardroomvoting.  *)

Time MetaCoq Run
     (t <- liquidity_extraction_specialize PREFIX TT_remap TT_rename to_inline BV_MODULE ;;
      tmDefinition BV_MODULE.(lmd_module_name) t
     ).

Print liquidity_boardroomvoting.

(** We redirect the extraction result for later processing and compiling with the Liquidity compiler *)
Redirect "examples/liquidity-extract/BoardroomVoting.liq" Compute liquidity_boardroomvoting.

(** * Extraction of a counter contract with refinement types to Liquidity *)

(** The contract uses refinement types to specify some functional correctness properties *)

From Coq Require Import PeanoNat ZArith.

From ConCert.Extraction Require Import LPretty LiquidityExtract Common.
From ConCert.Execution Require Import Blockchain Common.

From Coq Require Import List String.
Local Open Scope string_scope.

From MetaCoq.Template Require Import All.

Import ListNotations.
Import MonadNotation.
Import AddressMap.

Open Scope Z.

Definition PREFIX := "".

From ConCert.Execution.Examples Require Import BoardroomVotingTest.
Import Params.
(* Get string representation of modulus, and remap it. This way we avoid having the extraction compute the number. *)
Definition modulus_ := StringExtra.string_of_Z BoardroomVotingTest.modulus.

Print BoardroomMath.BoardroomAxioms.
(* TODO: remap all definition in boardroomaxioms *)
(* Definition TT_boardroomaxioms : list (kername * string) :=
  [
    elmeqb_spec : 
    zero 
    one 
    add : A -> A -
    mul : A -> A -
    opp : A -
    inv : A -
    pow : A -> Z -
    order 
    expeq := fun e e' : Z => e mod (order - 1) = e' mod (order - 
    order_ge_2 : order >
  ] *)
Print Params.
  Definition eqlemeqb_Z := @BoardroomMath.elmeqb _ Params.axioms.
  
  (* elmeq a b := a mod p = b mod p;
     elmeqb a b := a mod p =? b mod p;
     zero := 0;
     one := 1;
     add a a' := (a + a') mod p;
     mul a a' := (a * a') mod p;
     opp a := p - a;
     inv a := Zp.mod_inv a p;
     pow a e := Zp.mod_pow a e p;
     order := p; *)

(** A translation table for definitions we want to remap. The corresponding top-level definitions will be *ignored* *)
Definition TT_remap : list (kername * string) :=
  TT_remap_default ++ [
    remap <%% Amount %%> "tez"
  ;  remap <%% positive %%> "nat"
  ; remap <%% Z %%> "int"
  ; remap <%% Z.of_nat %%> "%int"
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
  ; remap <%% N.lxor %%> "xor"
  ; remap <%% N.succ_pos %%> "(addNat 1)"

  ; remap <%% BoardroomVotingTest.oneN %%> "1"
  ; remap <%% BoardroomVotingTest.four %%> "4"
  ; remap <%% BoardroomVotingTest.seven %%> "7"
  ; remap <%% BoardroomVotingTest._1234583932 %%> "1234583932"
  ; remap <%% BoardroomVotingTest._23241 %%> "23241"
  ; remap <%% BoardroomVotingTest._159338231 %%> "159338231"
  ; remap <%% BoardroomVotingTest._5 %%> "5"
  ; remap <%% BoardroomVotingTest._3 %%> "3"
  ; remap <%% BoardroomVotingTest._11 %%> "11"
  ; remap <%% BoardroomVotingTest.five %%> "5"
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

  ; remap <%% BoardroomMath.Zp.mod_pow %%> "mod_powInt"
  ; remap <%% BoardroomMath.Zp.mod_inv %%> "mod_invInt"
  (*; remap <%% @BoardroomMath.add%%> "addInt"
  ; remap <%% @BoardroomMath.elmeq%%> "eqInt"
  ; remap <%% @BoardroomMath.expeq%%> "expeq"
  ; remap <%% @BoardroomMath.elmeqb%%> "eqInt"
  ; remap <%% @BoardroomMath.zero%%> "0"
  ; remap <%% @BoardroomMath.one%%> "1"
  ; remap <%% @BoardroomMath.mul%%> "mulInt"
  ; remap <%% @BoardroomMath.opp%%> "-"
  ; remap <%% @BoardroomMath.inv%%> "inv"
  ; remap <%% @BoardroomMath.pow%%> "pow"
  ; remap <%% @BoardroomMath.order%%> "order"
  ; remap <%% @BoardroomVotingTest.axioms%%> "" *)

  (* ; remap <%% BV.verify_secret_vote_proof %%> "verify_secret_vote_proof" *)
  (* ; remap <%% @BV.make_signup_msg %%> "make_signup_msg" *)
  (* ; remap <%% @BV.make_commit_msg %%> "make_commit_msg" *)
  (* ; remap <%% @BV.make_vote_msg %%> "make_vote_msg" *)
  (* ; remap <%% @BV.secret_vote_proof %%> "secret_vote_proof" *)
  (* ; remap <%% @BV.secret_key_proof %%> "secret_key_proof" *)
  (* ; remap <%% @BV.hash_sk_data %%> "hash_sk_data" *)
  (* ; remap <%% @BV.hash_sv_data %%> "hash_sv_data" *)

  (* ; remap <%% @BV.handle_signup %%> "handle_signup" *)
  ; remap <%% @BV.handle_commit_to_vote %%> "handle_commit_to_vote"
  ; remap <%% @BV.handle_submit_vote %%> "handle_submit_vote"
  ; remap <%% @BV.handle_tally_votes %%> "handle_tally_votes"


  ; remap <%% BoardroomVotingTest.modulus %%> modulus_
  ; remap <%% @modulus_prime %%> "modulus_prime"
  ; remap <%% BV.encodeA %%> "%nat"
  ; remap <%% BV.encodeNat %%> "%nat"
  

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
  ; ("Zpos" ,"%int")
  ; ("Npos" ,"(fun (n:nat) -> n)")
  ; ("Zneg" ,"-")
  ; ("Z0" ,"0")
  ; ("N0" ,"0")
  ; ("xH" ,"0")
  ; ("1" ,"1")
  ; ("nil", "[]")
  ; ("true", "true")
  ; (string_of_kername <%% BV.State %%>, "State")  (* we add [storage] so it is printed without the prefix *) 
  ; ("tt", "()")
  ].
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
    let x := BV.secret_key_proof 0 _5 five in
    None.

Definition BV_MODULE : LiquidityMod msg init_ctx BV.Setup BV.State ActionBody :=
  {| (* a name for the definition with the extracted code *)
    lmd_module_name := "liquidity_boardroomvoting" ;

    (* definitions of operations on pairs and ints *)
    lmd_prelude := concat nl [prod_ops;int_ops];

    (* initial storage *)
    lmd_init := dummy_init ;

    (* no extra operations in [init] are required *)
    lmd_init_prelude := "" ;

    (* the main functionality *)
    lmd_receive := dummy_receive;

    (* code for the entry point *)
    lmd_entry_point := printWrapper (PREFIX ++ "receive_wrapper") ++ nl
                      ++ printMain |}.

(** We run the extraction procedure inside the [TemplateMonad].
    It uses the certified erasure from [MetaCoq] and the certified deboxing procedure
    that removes application of boxes to constants and constructors. *)
(* Require Import RecordSet. *)
Print Params.
Definition inline_boardroom_params : list kername :=
  [
      <%% Params.A %%>
    ; <%% Params.H %%>
    ; <%% Params.ser %%>
    (* ; <%% Params.axioms %%> *)
    ; <%% Params.gen %%>
    ; <%% Params.discr_log %%>
    (* ; <%% BoardroomVotingTest.axioms_instance %%> *)
    (* ; <%% BVZAxioms.boardroom_axioms_Z %%> *)

    (* ; <%% @BoardroomMath.oeq_equivalence %%> *)
    (* ; <%% @BoardroomMath.generator_instance %%> *)
    (* ; <%% @BoardroomMath.generator %%> *)
    (* ; <%% @BoardroomMath.generator_nonzero %%> *)
    (* ; <%% @BoardroomMath.generator_generates %%> *)
    (* ; <%% @BoardroomMath.log %%>
    ; <%% @BoardroomMath.log_proper %%>
    ; <%% @BoardroomMath.log_1_l %%>
    ; <%% @BoardroomMath.log_generator %%> *)

    (* BoardroomAxioms *)
    (* ; <%% @BoardroomMath.BoardroomAxioms%%>
    ; <%% @BoardroomMath.add%%>
    ; <%% @BoardroomMath.elmeq%%>
    ; <%% @BoardroomMath.expeq%%>
    ; <%% @BoardroomMath.elmeqb%%>
    ; <%% @BoardroomMath.zero%%>
    ; <%% @BoardroomMath.one%%>
    ; <%% @BoardroomMath.mul%%>
    ; <%% @BoardroomMath.opp%%>
    ; <%% @BoardroomMath.inv%%>
    ; <%% @BoardroomMath.pow%%>
    ; <%% @BoardroomMath.order%%> *)

    (* ; <%% @BoardroomMath.plus_expeq_proper%%>
    ; <%% @BoardroomMath.mul_expeq_proper%%>
    ; <%% @BoardroomMath.sub_expeq_proper%%>
    ; <%% @BoardroomMath.opp_expeq_proper%%>
    ; <%% @BoardroomMath.pow_generator_proper%%>
    ; <%% @BoardroomMath.prod_perm_proper%%>
    ; <%% @BoardroomMath.bruteforce_tally_aux_proper%%>
    ; <%% @BoardroomMath.bruteforce_tally_proper%%>
    ; <%% @BoardroomMath.elmeqb_elmeq_proper%%>

    ; <%% @BoardroomMath.elmeqb_spec%%>
    ; <%% @BoardroomMath.order_ge_2%%>
    ; <%% @BoardroomMath.elmeq_equiv%%>
    ; <%% @BoardroomMath.add_proper%%>
    ; <%% @BoardroomMath.mul_proper%%>
    ; <%% @BoardroomMath.opp_proper%%>
    ; <%% @BoardroomMath.inv_proper%%>
    ; <%% @BoardroomMath.pow_base_proper%%>
    ; <%% @BoardroomMath.pow_exp_proper%%>
    ; <%% @BoardroomMath.one_neq_zero%%>
    ; <%% @BoardroomMath.add_comm %%>
    ; <%% @BoardroomMath.add_assoc %%>
    ; <%% @BoardroomMath.mul_comm %%>
    ; <%% @BoardroomMath.mul_assoc %%>
    ; <%% @BoardroomMath.add_0_l %%>
    ; <%% @BoardroomMath.mul_0_l %%>
    ; <%% @BoardroomMath.mul_1_l %%>
    ; <%% @BoardroomMath.opp_inv_l %%>
    ; <%% @BoardroomMath.inv_inv_l %%>
    ; <%% @BoardroomMath.mul_add %%>
    ; <%% @BoardroomMath.pow_0_r %%>
    ; <%% @BoardroomMath.pow_1_r %%>
    ; <%% @BoardroomMath.pow_opp_1 %%>
    ; <%% @BoardroomMath.pow_plus %%>
    ; <%% @BoardroomMath.pow_pow %%>
    ; <%% @BoardroomMath.pow_nonzero %%>
    ; <%% @BoardroomMath.inv_nonzero %%> *)
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

Time MetaCoq Run
     (t <- liquidity_extraction_specialize PREFIX TT_remap TT_rename to_inline BV_MODULE ;;
      tmDefinition BV_MODULE.(lmd_module_name) t
     ).

Print liquidity_boardroomvoting.

(** We redirect the extraction result for later processing and compiling with the Liquidity compiler *)
Redirect "examples/liquidity-extract/BoardroomVoting.liq" Compute liquidity_boardroomvoting.

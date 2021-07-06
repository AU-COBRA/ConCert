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

(** A translation table for definitions we want to remap. The corresponding top-level definitions will be *ignored* *)
Definition TT_remap : list (kername * string) :=
  TT_remap_default ++ [
      remap <%% Amount %%> "tez"
    ; remap <%% Z %%> "int"
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

  (* ; remap <%% BV.verify_secret_vote_proof %%> "verify_secret_vote_proof" *)
  (* ; remap <%% @BV.make_signup_msg %%> "make_signup_msg" *)
  (* ; remap <%% @BV.make_commit_msg %%> "make_commit_msg" *)
  (* ; remap <%% @BV.make_vote_msg %%> "make_vote_msg" *)
  (* ; remap <%% @BV.secret_vote_proof %%> "secret_vote_proof" *)
  (* ; remap <%% @BV.secret_key_proof %%> "secret_key_proof" *)
  (* ; remap <%% @BV.hash_sk_data %%> "hash_sk_data" *)
  ; remap <%% @BV.hash_sv_data %%> "hash_sv_data"

  ; remap <%% @BV.handle_signup %%> "handle_signup"
  ; remap <%% @BV.handle_commit_to_vote %%> "handle_commit_to_vote"
  (* ; remap <%% @BV.handle_submit_vote %%> "handle_submit_vote" *)
  (* ; remap <%% @BV.handle_tally_votes %%> "handle_tally_votes" *)


  ; remap <%% BoardroomVotingTest.modulus %%> modulus_

  (* ; remap <%% @modulus_prime %%> "modulus_prime" *)
  (* ; remap <%% @generator_is_generator %%> "generator_is_generator" *)
  (* ; remap <%% @BoardroomMath.boardroom_axioms_Z %%> "BoardroomMath.boardroom_axioms_Z" *)
  (* ; remap <%% @BoardroomMath.Generator %%> "BoardroomAxioms" *)
  (* ; remap <%% @BoardroomMath.DiscreteLog %%> "BoardroomAxioms" *)
  

  ; remap <%% @List.map %%> "map"
  ; remap <%% @List.find %%> "find"
  ; remap <%% @countable.encode %%> "TODO_encode"
  ; remap <%% @Serializable.serialize %%> "TODO_serialize"
  ; remap <%% @Serializable.deserialize %%> "TODO_deserialize"
  ].
(** A translation table of constructors and some constants. The corresponding definitions will be extracted and renamed. *)
Definition TT_rename : list (string * string):=
  [ ("Some", "Some")
  ; ("None", "None")
  ; ("Z0" ,"0")
  ; ("nil", "[]")
  ; ("true", "true")
  ; (string_of_kername <%% BV.State %%>, "State")  (* we add [storage] so it is printed without the prefix *) 
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
    let x := BoardroomMath.add 1 2 in
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
    ; <%% Params.axioms %%>
    ; <%% Params.gen %%>
    ; <%% Params.discr_log %%>
    ; <%% BoardroomVotingTest.axioms_instance %%>
    (* this *)
    ; <%% BoardroomMath.boardroom_axioms_Z %%>

    (* BoardroomAxioms *)
    ; <%% @BoardroomMath.add%%>
    (* ; <%% @BoardroomMath.elmeq%%> *)
    ; <%% @BoardroomMath.elmeqb%%>
    ; <%% @BoardroomMath.zero%%>
    ; <%% @BoardroomMath.one%%>
    ; <%% @BoardroomMath.mul%%>
    ; <%% @BoardroomMath.opp%%>
    ; <%% @BoardroomMath.inv%%>
    ; <%% @BoardroomMath.pow%%>
    ; <%% @BoardroomMath.order%%>

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


  ].

(* Definition asd := (BoardroomMath.add 1 2).

Time MetaCoq Quote Recursively Definition ex1 := asd.
Check ex1.
Definition r1 := Eval vm_compute in (liquidity_extract_single TT_remap TT_rename true BV_MODULE.(lmd_prelude) "harness?" ex1).
Print r1. *)

Time MetaCoq Run
     (t <- liquidity_extraction_specialize PREFIX TT_remap TT_rename to_inline BV_MODULE ;;
      tmDefinition BV_MODULE.(lmd_module_name) t
     ).

Print liquidity_boardroomvoting.

(** We redirect the extraction result for later processing and compiling with the Liquidity compiler *)
Redirect "examples/liquidity-extract/CounterRefinementTypes.liq" Compute liquidity_counter.

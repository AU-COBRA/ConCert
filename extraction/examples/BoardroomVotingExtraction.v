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

(** A translation table for definitions we want to remap. The corresponding top-level definitions will be *ignored* *)
Definition TT_remap : list (kername * string) :=
  (* [ remap <%% bool %%> "bool"
  ; remap <%% list %%> "list"
  ; remap <%% Amount %%> "tez"
  ; remap <%% option %%> "option"
  ; remap <%% Z.add %%> "addInt"
  ; remap <%% Z.sub %%> "subInt"
  ; remap <%% Z.leb %%> "leInt"
  ; remap <%% Z.ltb %%> "ltInt"
  ; remap <%% Z %%> "int"
  ; remap <%% nat %%> "key_hash" (* type of account addresses*)
  ; remap <%% @fst %%> "fst"
  ; remap <%% @snd %%> "snd" ]. *)
  TT_remap_default ++ [
    remap <%% @ContractCallContext %%> "(address * (address * int))"
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

  ; remap <%% Nat.ltb %%> "ltbNat"

  ; remap <%% BV.verify_secret_vote_proof %%> "verify_secret_vote_proof"
  ; remap <%% @BV.make_signup_msg %%> "make_signup_msg"
  ; remap <%% @BV.make_commit_msg %%> "make_commit_msg"
  ; remap <%% @BV.make_vote_msg %%> "make_vote_msg"
  ; remap <%% @BV.secret_vote_proof %%> "secret_vote_proof"
  ; remap <%% @BV.secret_key_proof %%> "secret_key_proof"
  ; remap <%% @BV.hash_sk_data %%> "hash_sk_data"
  ; remap <%% @BV.hash_sv_data %%> "hash_sv_data"

  ; remap <%% @BV.handle_signup %%> "handle_signup"
  ; remap <%% @BV.handle_commit_to_vote %%> "handle_commit_to_vote"
  ; remap <%% @BV.handle_submit_vote %%> "handle_submit_vote"
  ; remap <%% @BV.handle_tally_votes %%> "handle_tally_votes"


  ; remap <%% BoardroomVotingTest.modulus %%> "13"

  ; remap <%% @BoardroomMath.BoardroomAxioms %%> "BoardroomAxioms"
  ; remap <%% @BoardroomMath.Generator %%> "BoardroomAxioms"
  ; remap <%% @BoardroomMath.DiscreteLog %%> "BoardroomAxioms"
  
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


Definition BV_MODULE : LiquidityMod msg init_ctx BV.Setup BV.State ActionBody :=
  {| (* a name for the definition with the extracted code *)
    lmd_module_name := "liquidity_boardroomvoting" ;

    (* definitions of operations on pairs and ints *)
    lmd_prelude := concat nl [prod_ops;int_ops];

    (* initial storage *)
    lmd_init := init_wrapper ;

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
Require Import RecordSet.

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
  ++
  [
    <%% Monads.Monad_option %%>
  (* ; <%% @Monads.MonadTrans %%> *)
  ; <%% @contract_initer_monad %%>
  ; <%% @run_contract_initer %%>
  ; <%% @contract_receiver_monad %%>
  ; <%% @contract_reader_to_contract_initer %%>
  ; <%% @option_to_contract_initer %%>
  ; <%% @contract_reader_to_receiver %%>
  ; <%% @option_to_contract_receiver %%>

  (* Dont work *)
  (* ; <%% @ContractIniter %%> *)
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


(* Time MetaCoq Run
     (t <- liquidity_extraction_specialize PREFIX TT_remap TT_rename to_inline BV_MODULE ;;
      tmDefinition BV_MODULE.(lmd_module_name) t
     ). *)

Print liquidity_boardroomvoting.

(** We redirect the extraction result for later processing and compiling with the Liquidity compiler *)
Redirect "examples/liquidity-extract/CounterRefinementTypes.liq" Compute liquidity_counter.

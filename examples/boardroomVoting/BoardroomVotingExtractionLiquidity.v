(** * Extraction of the Boardroom voting contract Liquidity *)

(** NOTE: Currently does not compile due to some restrictions on closures in Liquidity. Moreover, the printing of literals might need adjustments. *)

From MetaCoq.Template Require Import All.
From ConCert.Extraction Require Import LiquidityPretty.
From ConCert.Extraction Require Import LiquidityExtract.
From ConCert.Extraction Require Import Common.
From ConCert.Execution Require Import Blockchain.
From ConCert.Execution Require Import ContractCommon.
From ConCert.Execution Require Import ContractMonads.
From ConCert.Execution Require Import ResultMonad.
From ConCert.Execution Require Monad.
From ConCert.Execution Require OptionMonad.
From ConCert.Execution.Test Require Import LocalBlockchain.
From ConCert.Examples.BoardroomVoting Require Import BoardroomVotingZ.
From Coq Require Import ZArith.
From Coq Require Import List.
From Coq Require Import String.

Import MCMonadNotation.

Local Open Scope string_scope.
Open Scope Z.

Definition PREFIX := "".


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

Definition AddrSize := (2^128)%N.

#[local]
Instance Base : ChainBase := LocalBlockchain.LocalChainBase AddrSize.

Module Params <: BoardroomParams.
  Definition H : list positive -> positive := hash_func.
  Definition Base := Base.
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

(* A pseudo-random generator for secret keys *)
Definition sk n := (Z.of_nat n + _1234583932) * (modulus - _23241)^_159338231.

(* Make a list of secret keys, here starting at i=7 *)
Definition sks : list Z := map sk (seq seven num_parties).

(* Make a list of votes for each party *)
Definition svs : list bool :=
  Eval compute in map (fun _ => true)
                      (seq 0 votes_for)
                  ++ map (fun _ => false)
                         (seq 0 (num_parties - votes_for)).

(* Get string representation of modulus, and remap it. This way we avoid having the extraction compute the number. *)
Definition modulus_ := StringExtra.string_of_Z modulus.

Definition init_ctx := (Chain × ContractCallContext).

Definition init_wrapper (cctx : init_ctx) := (run_contract_initer BV.init) cctx.1 cctx.2.

Notation msg := (Chain × ContractCallContext × option BV.Msg).

Definition receive_wrapper (msg : msg)
                           (st : BV.State)
                           : result (list ActionBody * BV.State) Error :=
  match (run_contract_receiver BV.receive) msg.1 msg.2.1 st msg.2.2 with
  | Ok (st, acts) => Ok (acts, st)
  | Err e => Err e
  end.

Definition dummy_init : init_ctx -> BV.Setup -> result BV.State Error := fun _ _ => Err default_error.

Definition dummy_receive : msg -> BV.State -> result (list ActionBody × BV.State) Error :=
  fun m s =>
    let x := handle_signup 0 (0, 0) s s.(owner) 0%nat in
    Err default_error.

Definition storage_alias := "type storage = state".

Definition bruteforce_tally_def :=
 "let bruteforce_tally_aux =
  let rec bruteforce_tally_aux (n, votes_product) =
    if elmeqb (pow_p generator (int n)) votes_product then
        Some (n)
    else if n = 0p then
      None
    else
      let n0 = n - 1p in
        (bruteforce_tally_aux (unsafe_int_to_nat n0, votes_product))
  in fun n votes_product -> bruteforce_tally_aux (n, votes_product)".

Definition extra_ops :=
 "let unsafe_int_to_nat (n : int) =
    let n = match%nat n with
    | Plus n -> n
    | Minus _ -> failwith ""n shound not be negative"" in
    n
  let predN (n : nat) = unsafe_int_to_nat (n - 1p)

  let nth = let rec nth (n, l, default) =
  if n = 0p then (match l with
  [] -> default
   | x :: l' -> x)
  else let m = predN n in (match l with
  [] -> default
   | x :: t -> (nth (m, t, default)))
   in fun n l default -> nth (n, l, default)

  let prod (l : int list) =
    List.fold (fun (a, b) -> mulInt a b) l 1

  let firstn (n : nat) (l : 'a list) =
    let (_,r) = List.fold (fun (b,(n, a)) ->
        if n = 0p then (0p, a)
        else (predN n, b :: a)) l (n,[]) in
    List.rev r

  let skipn = let rec skipn (n, l) =
  if n = 0p then l
   else let n0 = predN n in (match l with
  [] -> []
   | a :: l0 -> (skipn (n0, l0)))
   in fun n l -> skipn (n, l)

  let existsb (f : 'a -> bool) = let rec existsb (l) =
  match l with
  [] -> false
   | a :: l0 -> (if (f a) then true else (existsb (l0)))
   in fun l -> existsb (l)".

Definition hash_func_def := "let hash_func (l : ((nat) list)) = addNat 1p (List.fold (fun (p,a) -> lxorNat p a) l 1p)".


Definition BV_MODULE : LiquidityMod msg init_ctx BV.Setup BV.State ActionBody Error :=
  {| (* a name for the definition with the extracted code *)
    lmd_module_name := "liquidity_boardroomvoting" ;

    (* definitions of operations on pairs and ints *)
    lmd_prelude := concat nl [LiquidityPrelude; extra_ops; hash_func_def];

    (* initial storage *)
    lmd_init := dummy_init;

    (* no extra operations in [init] are required *)
    lmd_init_prelude := "" ;

    (* the main functionality *)
    lmd_receive := dummy_receive;

    (* code for the entry point *)
    lmd_entry_point := storage_alias ++ nl
                      ++ printWrapper (PREFIX ++ "receive_wrapper") ++ nl
                      ++ printMain |}.

Definition inline_boardroom_params : list kername :=
  [  <%% Params.H %%>
    ; <%% Params.generator %%>
  ].


Definition inline_contract_monad_projection : list kername :=
  [  <%% @ContractMonads.chain_height %%>
    ; <%% @ContractMonads.current_slot %%>
    ; <%% @ContractMonads.finalized_height %%>
    ; <%% @ContractMonads.caller_addr %%>
    ; <%% @ContractMonads.my_addr %%>
    ; <%% @ContractMonads.my_balance %%>
    ; <%% @ContractMonads.call_amount %%>
    ; <%% @ContractMonads.deployment_setup %%>
    ; <%% @ContractMonads.reject_deployment %%>
    ; <%% @ContractMonads.accept_deployment %%>
    ; <%% @ContractMonads.call_msg %%>
    ; <%% @ContractMonads.my_state %%>
    ; <%% @ContractMonads.queue %%>
    ; <%% @ContractMonads.reject_call %%>
    ; <%% @ContractMonads.accept_call %%>
    ; <%% @ContractMonads.build_contract %%>
  ].


Definition to_inline : list kername :=
     inline_contract_monad_projection
  ++ inline_boardroom_params
  ++ [
    <%% OptionMonad.Monad_option %%>
  ; <%% @ConCert.Execution.ResultMonad.Monad_result %%>
  ; <%% ContractIniterSetupState %%>
  ; <%% ContractReceiverStateMsgState %%>
  ; <%% @contract_initer_monad %%>
  ; <%% @run_contract_initer %%>
  ; <%% @run_contract_receiver %%>
  ; <%% @contract_receiver_monad %%>
  ; <%% @contract_reader_to_contract_initer %%>
  ; <%% @result_to_contract_initer %%>
  ; <%% @contract_reader_to_receiver %%>
  ; <%% @result_to_contract_receiver %%>

  ; <%% @ContractReceiver %%>
  ; <%% @ContractIniter %%>

  ; <%% @Monad.bind %%>
  ; <%% @Monad.ret %%>
  ; <%% @Monad.lift %%>
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

(* Time MetaCoq Run ('(env, init_nm, receive_nm) <- quote_and_preprocess to_inline BV_MODULE ;;
                  tmDefinition "bv_env" env ;;
                  tmDefinition "bv_init_nm" init_nm ;;
                  tmDefinition "bv_receive_nm" receive_nm). *)


(** A translation table for definitions we want to remap. The corresponding top-level definitions will be *ignored* *)
Definition TT_remap : list (kername * string) :=
  [
    remap <%% Amount %%> "tez"
  ; remap <%% BV.amount_eqb %%> "eqTez"
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
  ; remap <%% Nat.ltb %%> "ltNat"
  ; remap <%% Z.modulo %%> "modInt"
  ; remap <%% Z.mul %%> "mulInt"
  ; remap <%% N.lxor %%> "lxorNat"
  ; remap <%% N.succ_pos %%> "addNat 1p"
  ; remap <%% mod_pow %%> "mod_pow"
  ; remap <%% Egcd.egcd %%> "egcd"
  ; remap <%% bruteforce_tally_aux %%> (bruteforce_tally_def ++ "in bruteforce_tally_aux")
  ; remap <%% @List.existsb %%> "existsb"
  ; remap <%% @List.nth %%> "nth"
  ; remap <%% @List.firstn %%> "firstn"
  ; remap <%% @List.skipn %%> "skipn"
  ; remap <%% Euler.prod %%> "prod"

  ; remap <%% hash_func %%> "hash_func"
  (* ; remap <%% oneN %%> "1p" *)
  (* ; remap <%% onePos %%> "1p" *)
  ; remap <%% four %%> "4p"
  ; remap <%% seven %%> "7p"
  ; remap <%% _1234583932 %%> "1234583932"
  ; remap <%% _23241 %%> "23241"
  ; remap <%% _159338231 %%> "159338231"
  ; remap <%% _5 %%> "5"
  ; remap <%% _3 %%> "3p"
  ; remap <%% Z3 %%> "3"
  ; remap <%% _11 %%> "11"
  ; remap <%% @ActionBody %%> "operation"
  ; remap <%% @ContractCallContext %%> "(address * (address * (tez * tez)))"
  ; remap <%% @Chain %%> "(nat * (nat * nat))" (* chain_height, current_slot, finalized_height *)
  ; remap <%% @chain_height %%> "fst" (* small hack, but valid since ContractCallContext is mapped to a tuple *)
  ; remap <%% @Blockchain.current_slot %%> "(fun c -> c.(1).(0))" (* small hack, but valid since Chain is mapped to a tuple *)
  ; remap <%% @finalized_height %%> "(fun c -> snd (snd c)" (* small hack, but valid since Chain is mapped to a tuple *)
  ; remap <%% @ctx_from %%> "fst" (* small hack, but valid since ContractCallContext is mapped to a tuple *)
  ; remap <%% @ctx_amount %%> "(fun c -> c.(1).(1).(1))" (* small hack, but valid since ContractCallContext is mapped to a tuple *)
  ; remap <%% @ctx_contract_address %%> "(fun c -> c.(1).(0))" (* small hack, but valid since ContractCallContext is mapped to a tuple *)
  ; remap <%% @ctx_contract_balance %%> "(fun c -> c.(1).(1).(0))" (* small hack, but valid since ContractCallContext is mapped to a tuple *)
  ; remap <%% @AddressMap.add %%> "Map.add"
  ; remap <%% @AddressMap.find %%> "Map.find"
  ; remap <%% @AddressMap.of_list %%> "Map.of_list"
  ; remap <%% @AddressMap.values %%> "Map.values"
  ; remap <%% @AddressMap.keys %%> "Map.keys"
  ; remap <%% @AddressMap.empty %%> "(Map [])"

  ; remap <%% modulus %%> modulus_
  ; remap <%% BV.encodeA %%> "unsafe_int_to_nat"
  ; remap <%% BV.encodeNat %%> ""

  ; remap <%% @List.fold_left %%> "List.fold"
  ; remap <%% @List.map %%> "List.map"
  ; remap <%% @List.find %%> "List.find"
  ; remap <%% @List.length %%> "List.length"
  ; remap <%% @List.app %%> "List.append"
  ].

(** A translation table of constructors and some constants. The corresponding definitions will be extracted and renamed. *)
Definition TT_rename : list (string * string) :=
  [ ("Some", "Some")
  ; ("None", "None")
  ; ("Zpos" ,"int")
  ; ("Npos" ,"")
  ; ("Zneg" ,"-")
  ; ("Z0" ,"0")
  ; ("0" ,"0p")
  ; ("N0" ,"0p")
  ; ("xH" ,"0")
  ; ("1" ,"1")
  ; ("2" ,"2p")
  ; ("S" ,"1p +")
  ; ("nil", "[]")
  ; ("true", "true")
  ; ("false", "false")
  ; (String.to_string (string_of_kername <%% BV.State %%>), "state") (* we add [storage] so it is printed without the prefix *)
  ; ("tt", "()")
  ].

(* Time MetaCoq Run (
  t <- liquidity_prepare_extraction PREFIX TT_remap TT_rename to_inline BV_MODULE bv_env bv_init_nm bv_receive_nm ;;
  tmDefinition BV_MODULE.(lmd_module_name) t
  ).

(** We redirect the extraction result for later processing and compiling with the Liquidity compiler *)
Redirect "../extraction/tests/extracted-code/liquidity-extract/BoardroomVoting.liq" MetaCoq Run (tmMsg liquidity_boardroomvoting). *)

(** * Extraction of the Boardroom voting contract CameLIGO *)

(** We provide a configuration required for the contract extraction:
    additional remappings, definitions to inline, etc. *)

From Coq Require Import PeanoNat ZArith.

From ConCert.Extraction Require Import LPretty CameLIGOExtract Common.
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
Definition generator : Z := 3.

Definition hash_func (l : list positive) : positive :=
  N.succ_pos (fold_left (fun a p => N.lxor (Npos p) a) l 1%N).

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

(* Get string representation of modulus, and remap it. This way we avoid having the extraction compute the number. *)
Definition modulus_ := StringExtra.string_of_Z modulus.

Require Import ContractMonads.

Definition setupWchain := (BV.Setup × Chain).

Definition init_wrapper (cctx : ContractCallContext) (s : setupWchain) := (run_contract_initer BV.init) s.2 cctx s.1.

Definition receive_wrapper (c : Chain)
                           (ctx : ContractCallContext)
                           (st : BV.State) 
                           (msg : option BV.Msg)
                           : option (list ActionBody * BV.State):= 
                           (* None. *)
  match (run_contract_receiver BV.receive) c ctx st msg with
  | Some (st, acts) => Some (acts, st)
  | None => None
  end.

Definition storage_alias := "type storage = state".
Definition bruteforce_tally_def := 
 "(fun (votes :  (a) list) -> 
  let rec bruteforce_tally_aux  (n, votes_product : nat * a) : nat option = 
    if elmeqb (pow_p generator (int n)) votes_product then 
        Some (n) 
    else if n = 0n then 
      None
    else
      let n0 = n - 1n in
        (bruteforce_tally_aux (unsafe_int_to_nat n0, votes_product))
  in bruteforce_tally_aux ((List.length votes), (prod votes)))".

Definition extra_ops := 
 "let unsafe_int_to_nat (n : int) = abs(n)
  let predN (n : nat) = unsafe_int_to_nat (n - 1n)
  let mod_pow (a : int) (e : int) (p : int) : int = failwith (""unimplemented"")
  let egcd (a : int) (p : int) : int * int = failwith (""unimplemented"")
  
  let nth  = let rec nth  (n, l, default : nat * int list * int) : int = 
  if n = 0n then (match l with 
  []  -> default
   | x :: r -> x)
  else let m = predN n in (match l with 
  []  -> default
   | x :: t -> (nth (m, t, default)))
   in fun (n:nat) (l:int list) (default:int) -> nth (n, l, default)
   
   
  let prod (l : int list) =
    List.fold (fun (a, b: int*int) -> multInt a b) l 1
  
  let firstn (n : nat) (l : int list) : int list =
    let (_,r) = List.fold_left (fun ((n, a),b : (nat * int list) * int) ->
        if n = 0n then (0n, a)
        else (predN n, b :: a)) (n,([] : int list)) l in
   r
  
  let skipn  = let rec skipn  (n, l : nat * int list) : int list = 
   if n = 0n then l
    else let n0 = predN n in (match l with 
    | []  -> ([]:int list)
    | a :: l0 -> (skipn (n0, l0 : nat * int list)))
    in fun (n : nat) (l : int list) -> skipn (n, l : nat * int list)".


Definition existsb_def := 
  "(let existsb (f : voterInfo -> bool) = let rec existsb  (l: voterInfo list) : bool = 
  match l with 
  []  -> false
  | a :: l0 -> (if (f a) then true else (existsb (l0)))
  in fun (l: voterInfo list) -> existsb (l) in existsb)".

Definition hash_func_def := "let hash_func (l :  (nat) list) = addN 1n (List.fold_left (fun (a, p : nat * nat) -> Bitwise.xor p a) 1n l)".

Definition callctx := "(Tezos.sender,(Tezos.self_address,(Tezos.amount,Tezos.balance)))".


Definition BV_MODULE : CameLIGOMod BV.Msg ContractCallContext setupWchain BV.State ActionBody :=
  {| (* a name for the definition with the extracted code *)
    lmd_module_name := "cameligo_boardroomvoting" ;

    (* definitions of operations on pairs and ints *)
    lmd_prelude := concat nl [CameLIGOPretty.CameLIGOPrelude; extra_ops; hash_func_def];

    (* initial storage *)
    lmd_init := init_wrapper;

    (* no extra operations in [init] are required *)
    lmd_init_prelude := "";

    lmd_receive_prelude := "";
    (* the main functionality *)
    lmd_receive := receive_wrapper;

    (* code for the entry point *)
    lmd_entry_point := CameLIGOPretty.printWrapper (PREFIX ++ "receive_wrapper")
                        "msg"
                        "state"
                        ++ nl
                        ++ CameLIGOPretty.printMain "state" |}.

Definition inline_boardroom_params : list kername :=
  [
      <%% Params.H %%>
    ; <%% Params.generator %%>
  ].


Definition inline_contract_monad_projection : list kername := 
  [
      <%% @ContractMonads.chain_height %%>
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
    <%% Monads.Monad_option %%>
  ; <%% ContractIniterSetupState %%>
  ; <%% ContractReceiverStateMsgState %%>
  ; <%% @contract_initer_monad %%>
  ; <%% @run_contract_initer %%>
  ; <%% @run_contract_receiver %%>
  ; <%% @contract_receiver_monad %%>
  ; <%% @contract_reader_to_contract_initer %%>
  ; <%% @option_to_contract_initer %%>
  ; <%% @contract_reader_to_receiver %%>
  ; <%% @option_to_contract_receiver %%>
  
  ; <%% @ContractReceiver %%>
  ; <%% @ContractIniter %%>
  
  ; <%% @Monads.bind %%>
  ; <%% @Monads.ret %%>
  ; <%% @Monads.lift %%>
  ; <%% bool_rect %%>
  ; <%% bool_rec %%>
  ; <%% option_map %%>
  ; <%% @BV.isSome %%>
  ; <%% @isNone %%>
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

(** A translation table for definitions we want to remap. The corresponding top-level definitions will be *ignored* *)
Definition TT_remap : list (kername * string) :=
  [ remap <%% BV.amount_eqb %%> "eqTez"
  ; remap <%% positive %%> "nat"
  (* By default, [Z] is remapped to [tez] along with the operations.
     We override this behavior in the case of Boardroom voting *)
  ; remap <%% Z %%> "int"
  ; remap <%% Z.of_nat %%> "int"
  ; remap <%% Z.add %%> "addInt"
  ; remap <%% Z.sub %%> "subInt"
  ; remap <%% Z.leb %%> "leInt"
  ; remap <%% Z.ltb %%> "ltInt"
  ; remap <%% Z.add %%> "addInt"
  ; remap <%% Z.eqb %%> "eqInt"
  ; remap <%% Z.gtb %%> "gtbInt"
  ; remap <%% Nat.ltb %%> "ltbN"
  ; remap <%% Z.modulo %%> "modInt"
  ; remap <%% Z.mul %%> "multInt"
  ; remap <%% N.lxor %%> "Bitwise.xor"
  ; remap <%% N.succ_pos %%> "addN 1n"
  ; remap <%% mod_pow %%> "mod_pow"
  ; remap <%% hash_func %%> "hash_func"
  ; remap <%% Egcd.egcd %%> "egcd"
  ; remap <%% bruteforce_tally %%> bruteforce_tally_def (* inlined definition *)
  ; remap <%% @List.existsb %%> existsb_def (* inlined definition *)
  ; remap <%% @List.nth %%> "nth"
  ; remap <%% @List.firstn %%> "firstn"
  ; remap <%% @List.skipn %%> "skipn"
  ; remap <%% Euler.prod %%> "prod"

  ; remap <%% @ActionBody %%> "operation"
  ; remap <%% @AddressMap.add %%> "Map.add"
  ; remap <%% @AddressMap.find %%> "Map.find_opt"
  ; remap <%% @AddressMap.of_list %%> "Map.of_list"
  ; remap <%% @AddressMap.values %%> (* only way to obtain values is via fold - specialized to voterInfo*)
  "(fun (v:(address, voterInfo) map) ->
    Map.fold (fun (acc, (_,info) : voterInfo list * (address * voterInfo)) -> info :: acc)
    v ([]: voterInfo list))"
  ; remap <%% @AddressMap.keys %%> "Map.keys"
  ; remap <%% @AddressMap.empty %%> "Map.empty"

  ; remap <%% modulus %%> modulus_
  ; remap <%% BV.encodeA %%> "unsafe_int_to_nat"
  ; remap <%% BV.encodeNat %%> ""

  ; remap <%% @List.fold_left %%> "List.fold_left"
  ; remap <%% @List.map %%> "List.map"
  ; remap <%% @List.find %%> "List.find"
  ; remap <%% @List.length %%> "List.length"
  ; remap <%% @List.app %%> "List.fold_left (fun (acc, e : (int list) * int) -> e :: acc)" (* small hack since ligo doesn't have append on lists *)
  ].
(** A translation table of constructors and some constants. The corresponding definitions will be extracted and renamed. *)
Definition TT_rename : list (string * string):=
  [ ("Some", "Some")
  ; ("None", "None")
  ; ("Zpos" ,"int") (* [int] is an embedding of natutal numbers to integers in CameLIGO *)
  ; ("S" ,"1n +")
  ; ("true", "true")
  ; ("false", "false")
  ; ("hash", "hash_")
  ; (string_of_kername <%% BV.State %%>, "state")  (* we add [storage] so it is printed without the prefix *)
  ; ("tt", "()")
  ].

(* NOTE: the extraction process takes ~15 min. We comment out these lines to avoid the recompiling it for each build *)

(* Time MetaCoq Run (CameLIGO_prepare_extraction PREFIX to_inline TT_remap TT_rename [] "cctx_instance" BV_MODULE).

Time Definition cameLIGO_boardroomvoting := Eval vm_compute in cameligo_boardroomvoting_prepared.

Redirect "examples/extracted-code/cameligo-extract/BoardroomVoting.mligo"
MetaCoq Run (tmMsg cameLIGO_boardroomvoting). *)

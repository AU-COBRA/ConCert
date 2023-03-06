(** * Extraction of the Boardroom voting contract CameLIGO *)

(** We provide a configuration required for the contract extraction:
    additional remappings, definitions to inline, etc. *)
From MetaCoq.Template Require Import All.
From ConCert.Extraction Require Import CameLIGOExtract.
From ConCert.Extraction Require Import CameLIGOPretty.
From ConCert.Extraction Require Import Common.
From ConCert.Execution Require Import Blockchain.
From ConCert.Execution Require Import ContractCommon.
From ConCert.Execution Require Import ContractMonads.
From ConCert.Execution Require Import ResultMonad.
From ConCert.Execution Require Monad.
From ConCert.Execution Require OptionMonad.
From ConCert.Execution.Test Require Import LocalBlockchain.
From ConCert.Examples.BoardroomVoting Require Import BoardroomVotingZ.
From Coq Require Import List.
From Coq Require Import String.
From Coq Require Import ZArith.


Local Open Scope string_scope.
Open Scope Z.

#[local]
Existing Instance PrintConfShortNames.PrintWithShortNames.

Definition PREFIX := "".

(* In this example we just use xor for the hash function, which is
   obviously not cryptographically secure. *)
Definition modulus : Z := 201697267445741585806196628073.
Definition generator : Z := 3.

Definition hash_func (l : list positive) : positive :=
  N.succ_pos (fold_left (fun a p => N.lxor (Npos p) a) l 1%N).

  (* Instance Base : ChainBase := LocalChainBase AddrSize. *)
Definition AddrSize := (2^128)%N.

Module Params <: BoardroomParams.
  Parameter Base : ChainBase.
  Definition H : list positive -> positive := hash_func.
  Definition prime := modulus.
  Definition generator := generator.
End Params.
Module BV := BoardroomVoting Params. Import BV.

(* Get string representation of modulus, and remap it. This way we avoid having the extraction compute the number. *)
Definition modulus_ := StringExtra.string_of_Z modulus.

Definition setupWchain := (BV.Setup × Chain).

Definition init_wrapper (cctx : ContractCallContext) (s : setupWchain) := (run_contract_initer BV.init) s.2 cctx s.1.


(** In the Tezos blockchain there is no concept of initialization
    function. However, it's common to provide a function that computes
    a valid initial storage that can be used for deployment.*)
Definition init (s : Address * Setup) : result State Error :=
  if (finish_registration_by s.2 <? finish_vote_by s.2)%nat
      then
        Ok {| owner := s.1;
                registered_voters := AddressMap.empty;
                public_keys := [];
                setup := s.2;
               tally := None; |}
      else Err default_error.

Lemma init_eq_init_wrapper cctx s :
  init_wrapper cctx s = init (cctx.(ctx_from), s.1).
Proof.
  unfold init_wrapper,init. cbn.
  now destruct (_ <? _)%nat.
Qed.

Definition receive_wrapper (c : Chain)
                           (ctx : ContractCallContext)
                           (st : BV.State)
                           (msg : option BV.Msg)
                           : result (list ActionBody * BV.State) Error :=
  match (run_contract_receiver BV.receive) c ctx st msg with
  | Ok (st, acts) => Ok (acts, st)
  | Err e => Err e
  end.

Definition storage_alias := "type storage = state".
Definition bruteforce_tally_def :=
 "(fun (votes : (a) list) ->
  let rec bruteforce_tally_aux (n, votes_product : nat * a) : (nat, nat) result =
    if elmeqb (pow_p generator (int n)) votes_product then
        Ok (n)
    else if n = 0n then
      Err 0n
    else
      let n0 = n - 1n in
        (bruteforce_tally_aux (unsafe_int_to_nat n0, votes_product))
  in bruteforce_tally_aux ((List.length votes), (prod votes)))".

Definition extra_ops :=
 "let unsafe_int_to_nat (n : int) = abs(n)
  let predN (n : nat) = unsafe_int_to_nat (n - 1n)
  let mod_pow (a : int) (e : int) (p : int) : int = failwith (""unimplemented"")
  let egcd (a : int) (p : int) : int * int = failwith (""unimplemented"")

  let nth = let rec nth (n, l, default : nat * int list * int) : int =
  if n = 0n then (match l with
  [] -> default
   | x :: r -> x)
  else let m = predN n in (match l with
  [] -> default
   | x :: t -> (nth (m, t, default)))
   in fun (n:nat) (l:int list) (default:int) -> nth (n, l, default)


  let prod (l : int list) =
    List.fold (fun (a, b: int*int) -> multInt a b) l 1

  let firstn (n : nat) (l : int list) : int list =
    let (_,r) = List.fold_left (fun ((n, a),b : (nat * int list) * int) ->
        if n = 0n then (0n, a)
        else (predN n, b :: a)) (n,([] : int list)) l in
   r

  let skipn = let rec skipn (n, l : nat * int list) : int list =
   if n = 0n then l
    else let n0 = predN n in (match l with
    | [] -> ([]:int list)
    | a :: l0 -> (skipn (n0, l0 : nat * int list)))
    in fun (n : nat) (l : int list) -> skipn (n, l : nat * int list)".


Definition existsb_def :=
  "(let existsb (f : voterInfo -> bool) = let rec existsb (l: voterInfo list) : bool =
  match l with
  [] -> false
  | a :: l0 -> (if (f a) then true else (existsb (l0)))
  in fun (l: voterInfo list) -> existsb (l) in existsb)".

Definition hash_func_def := "let hash_func (l : (nat) list) = addN 1n (List.fold_left (fun (a, p : nat * nat) -> Bitwise.xor p a) 1n l)".

Definition callctx := "(Tezos.sender,(Tezos.self_address,(Tezos.amount,Tezos.balance)))".


Definition BV_MODULE : CameLIGOMod BV.Msg ContractCallContext (Address * Setup) BV.State ActionBody Error :=
  {| (* a name for the definition with the extracted code *)
    lmd_module_name := "cameligo_boardroomvoting" ;

    (* definitions of operations on pairs and ints *)
    lmd_prelude := concat nl [CameLIGOPretty.CameLIGOPrelude; extra_ops; hash_func_def];

    (* initial storage *)
    lmd_init := init;

    (* no extra operations in [init] are required *)
    lmd_init_prelude := "";

    lmd_receive_prelude := "";
    (* the main functionality *)
    lmd_receive := receive_wrapper;

    (* code for the entry point *)
    lmd_entry_point := CameLIGOPretty.printMain (PREFIX ++ "receive_wrapper")
                        "msg"
                        "state"
  |}.

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

  (* ; <%% @BV.set_State_owner %%> *)
  (* ; <%% @BV.set_State_registered_voters %%> *)
  (* ; <%% @BV.set_State_public_keys %%> *)
  (* ; <%% @BV.set_State_setup %%> *)
  (* ; <%% @BV.set_State_tally %%> *)

  (* ; <%% @BV.set_VoterInfo_voter_index %%> *)
  (* ; <%% @BV.set_VoterInfo_vote_hash %%> *)
  (* ; <%% @BV.set_VoterInfo_public_vote %%> *)

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
  ; remap <%% @List.app %%> "List.fold_left (fun (acc, e : (int list) * int) -> e :: acc)" (* small hack since LIGO doesn't have append on lists *)
  ].

(** A translation table of constructors and some constants. The corresponding definitions will be extracted and renamed. *)
Definition TT_rename : list (string * string) :=
  [ ("Some", "Some")
  ; ("None", "None")
  ; ("Zpos" ,"int") (* [int] is an embedding of natural numbers to integers in CameLIGO *)
  ; ("S" ,"1n +")
  ; ("true", "true")
  ; ("false", "false")
  ; ("hash", "hash_")
  ; (String.to_string (string_of_kername <%% BV.State %%>), "state") (* we add [storage] so it is printed without the prefix *)
  ; ("tt", "()")
  ].

Time MetaCoq Run (CameLIGO_prepare_extraction to_inline TT_remap TT_rename [] "cctx_instance" BV_MODULE).

Time Definition cameLIGO_boardroomvoting := Eval vm_compute in cameligo_boardroomvoting_prepared.

Redirect "../extraction/tests/extracted-code/cameligo-extract/BoardroomVoting.mligo"
MetaCoq Run (tmMsg (String.of_string cameLIGO_boardroomvoting)).

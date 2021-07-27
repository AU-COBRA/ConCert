(** * Extraction of Escrow to CameLIGO and liquidity*)

From Coq Require Import PeanoNat ZArith Notations Bool.

From MetaCoq.Template Require Import Loader.
From MetaCoq.Erasure Require Import Loader.

From ConCert Require Import MyEnv.
From ConCert.Extraction Require Import Common Extraction.
From ConCert.Embedding.Extraction Require Import SimpleBlockchainExt.
From ConCert.Execution Require Import Blockchain.
From ConCert.Execution.Examples Require Import Common.
  From ConCert.Extraction Require CameLIGOPretty CameLIGOExtract.

From Coq Require Import List Ascii String.
Require ContractMonads.

From MetaCoq.Template Require Import All.


From Coq Require Import List.
From Coq Require Import Morphisms.
From Coq Require Import ZArith.
From Coq Require Import Permutation.
From Coq Require Import Psatz.
Require Import Automation.
Require Import Blockchain.
Require Import Extras.
Require Import Monads.
Require Import ResultMonad.
Require Import Serializable.
From ConCert.Utils Require Import RecordUpdate.

Import ListNotations.
Import RecordSetNotations.
From ConCert.Execution Require Import Escrow.

Section Escrow.
Context `{ChainBase}.
Set Primitive Projections.
Set Nonrecursive Elimination Schemes.

(* workaround for extraction *)
Definition deadline : nat := 50.
Definition _4 : Z := 4.
Definition _3 : Z := 3.
Definition _2 : Z := 2.


Open Scope Z.
Open Scope bool_scope.
Definition init (chain : Chain) (ctx : ContractCallContext) (setup : Setup)
  : option State :=
  let seller := ctx_from ctx in
  let buyer := setup_buyer setup in
  if negb (buyer =? seller)%address && 
     negb (ctx_amount ctx =? 0) &&
     Z.even (ctx_amount ctx)
  then Some (build_state (current_slot chain) buyer_commit seller buyer 0 0)
  else None.

Definition receive
           (chain : Chain) (ctx : ContractCallContext)
           (state : State) (msg : option Msg)
  : option (State * list ActionBody) :=
  match msg, next_step state with
  | Some commit_money, buyer_commit =>
    let item_price := (ctx_contract_balance ctx - ctx_amount ctx) / _2 in
    let expected := item_price * _2 in
    if (ctx_from ctx =? buyer state)%address then 
      if ctx_amount ctx =? expected then 
      let new_state := {|
        last_action := current_slot chain;
        next_step := buyer_confirm;
        seller := state.(seller);
        buyer := state.(buyer);
        seller_withdrawable := state.(seller_withdrawable);
        buyer_withdrawable := state.(buyer_withdrawable);
      |} in
      Some (new_state, [])
      else None
    else None
  | Some confirm_item_received, buyer_confirm =>
    let item_price := ctx_contract_balance ctx / _4 in
    if (ctx_from ctx =? buyer state)%address then
      if ctx_amount ctx =? 0 then
      let new_state := {|
        last_action := state.(last_action);
        seller := state.(seller);
        buyer := state.(buyer);
        seller_withdrawable := item_price * _3;
        buyer_withdrawable := item_price;
        next_step := withdrawals;
      |} in
      Some (new_state, [])
      else None
    else None
  | Some withdraw, withdrawals =>
    if ctx_amount ctx =? 0 then
      let from := ctx_from ctx in
      match
        (match from =? buyer state, from =? seller state with
        | true, _ => Some (buyer_withdrawable state, state<|buyer_withdrawable := 0|>)
        | _, true => Some (seller_withdrawable state, state<|seller_withdrawable := 0|>)
        | _, _ => None
        end%address)
      with 
      | Some (to_pay, new_state) => 
        if 0 <? to_pay then
        let new_state := if (buyer_withdrawable new_state =? 0) && (seller_withdrawable new_state =? 0)
                         then new_state<|next_step := no_next_step|>
                         else new_state in
        Some (new_state, [act_transfer (ctx_from ctx) to_pay])
      else None
      | None => None
      end
    else None
  | Some withdraw, buyer_commit =>
    if (ctx_amount ctx =? 0)
       && negb (last_action state + deadline <? current_slot chain)%nat
       && (ctx_from ctx =? seller state)%address then
      let balance := ctx_contract_balance ctx in
      Some (state<|next_step := no_next_step|>, [act_transfer (seller state) balance])
    else None
  | _, _ => None
  end.

End Escrow.


Import ListNotations.
Import MonadNotation.
Import CameLIGOExtract.
Import CameLIGOPretty.
Open Scope Z.
Local Open Scope string_scope.

Definition PREFIX := "".

Section EscrowExtraction.

  Definition contractcallcontextDef := "type cctx = (address * (address * (tez * tez)))".

  (** A translation table for definitions we want to remap. The corresponding top-level definitions will be *ignored* *)
  Definition TT_remap_ligo : list (kername * string) :=
    [
      remap <%% Amount %%> "tez"
    ; remap <%% Nat.add %%> "addN"
    ; remap <%% Nat.ltb %%> "ltbN"
    ; remap <%% Nat.mul %%> "multN"
    ; remap <%% Z.add %%> "addTez"
    ; remap <%% Z.mul %%> "multTez"
    ; remap <%% Z.sub %%> "subTez"
    ; remap <%% Z.leb %%> "leTez"
    ; remap <%% Z.ltb %%> "ltTez"
    ; remap <%% Z.div %%> "divTez"
    ; remap <%% Z.even %%> "evenTez"
    ; remap <%% Z.eqb %%> "eqTez"
    ; remap <%% Z %%> "tez"

    ; remap <%% @ActionBody %%> "operation"
    ; remap <%% @ContractCallContext %%> "cctx"
    ; remap <%% @current_slot %%> "current_slot" (* small hack to avoid generating the definition of current_slot *)
    ; remap <%% @ctx_from %%> "(fun (c : cctx) -> c.0)" (* small hack, but valid since ContractCallContext is mapped to a tuple *)
    ; remap <%% @ctx_contract_address %%> "(fun (c : cctx) -> c.1.0)" (* small hack, but valid since ContractCallContext is mapped to a tuple *)
    ; remap <%% @ctx_contract_balance %%> "(fun (c : cctx) -> c.1.1.0)" (* small hack, but valid since ContractCallContext is mapped to a tuple *)
    ; remap <%% @ctx_amount %%> "(fun (c : cctx) -> c.1.1.1)" (* small hack, but valid since ContractCallContext is mapped to a tuple *)
    ; remap <%% @address_eqb %%> "eq_addr"

    ; remap <%% _2 %%> "2tez"
    ; remap <%% _3 %%> "3tez"
    ; remap <%% _4 %%> "4tez"
    ; remap <%% deadline %%> "50n"

    ; remap <%% @List.fold_left %%> "List.fold"
    ; remap <%% @List.map %%> "List.map"
    ; remap <%% @List.find %%> "List.find"
    ; remap <%% @List.length %%> "List.length"
    ; remap <%% @List.app %%> "List.append"
    ].
  (** A translation table of constructors and some constants. The corresponding definitions will be extracted and renamed. *)
  Definition TT_rename_ligo : list (string * string):=

    [ ("Some", "Some")
    ; ("None", "None")
    ; ("Zpos" ,"int")
    ; ("Npos" ,"(fun (n:nat) -> n)")
    ; ("Zneg" ,"-")
    ; ("Z0" ,"0tez")
    ; ("N0" ,"0")
    ; ("xH" ,"0")
    ; ("1" ,"1")
    ; ("nil", "[]")
    ; ("true", "true")
    ; ("tt", "()")
    ].
    
  Definition dummy_chain :=
        "type chain = {
          chain_height     : nat;
          current_slot     : nat;
          finalized_height : nat;
        }"
    ++ nl
    ++ "let dummy_chain : chain = {
          chain_height     = Tezos.level;
          current_slot     = Tezos.level;
          finalized_height = Tezos.level;
        }".

  Definition escrow_init_wrapper (cctx : ContractCallContext) (s : Setup * Chain) : option State := 
    EscrowExtract.init (snd s) cctx (fst s).
    
  Definition escrow_receive (c : Chain) (cctx : ContractCallContext) (s : State) (msg : option Msg) : option (list ActionBody * State) :=
    match EscrowExtract.receive c cctx s msg with
    | Some (s, acts) => Some (acts, s)
    | None => None
    end.
  
  Definition callctx := "(Tezos.sender, (Tezos.sender, (Tezos.amount, Tezos.balance)))".

  Definition ESCROW_MODULE_LIGO : CameLIGOMod Msg ContractCallContext (Setup * Chain) State ActionBody :=
    {| (* a name for the definition with the extracted code *)
      lmd_module_name := "cameligo_escrow" ;

      (* definitions of operations on pairs and ints *)
      lmd_prelude := String.concat nl [CameLIGOPrelude; dummy_chain; contractcallcontextDef];

      (* initial storage *)
      lmd_init := escrow_init_wrapper ;

      (* no extra operations in [init] are required *)
      lmd_init_prelude := "";

      (* the main functionality *)
      lmd_receive := escrow_receive ;

      lmd_receive_prelude := "";
      (* code for the entry point *)
      lmd_entry_point := printWrapper (PREFIX ++ "escrow_receive") 
                                      (PREFIX ++"msg") 
                                      "state" 
                                      callctx 
                                      ++ nl
                                      ++ CameLIGOPretty.printMain "state" |}.
  
  Definition to_inline : list kername := 
    [
      <%% Monads.Monad_option %%>
    ; <%% @Monads.bind %%>
    ; <%% @Monads.ret %%>
    ; <%% @Monads.lift %%>
    ; <%% bool_rect %%>
    ; <%% bool_rec %%>
    ; <%% option_map %%>
    ; <%% @Extras.with_default %%>
  
    ; <%% @setter_from_getter_State_last_action %%>
    ; <%% @setter_from_getter_State_next_step %%>
    ; <%% @setter_from_getter_State_seller %%>
    ; <%% @setter_from_getter_State_buyer %%>
    ; <%% @setter_from_getter_State_seller_withdrawable %%>
    ; <%% @setter_from_getter_State_buyer_withdrawable %%>

    ; <%% @set_State_last_action %%>
    ; <%% @set_State_next_step %%>
    ; <%% @set_State_seller %%>
    ; <%% @set_State_buyer %%>
    ; <%% @set_State_seller_withdrawable %%>
    ; <%% @set_State_buyer_withdrawable %%>

    ].
  Time MetaCoq Run
  (CameLIGO_prepare_extraction PREFIX to_inline TT_remap_ligo TT_rename_ligo callctx ESCROW_MODULE_LIGO).

  Time Definition cameLIGO_escrow := Eval vm_compute in cameligo_escrow_prepared.
  Print cameLIGO_escrow.
  Redirect "examples/cameligo-extract/EscrowExtract.mligo" MetaCoq Run (tmMsg cameLIGO_escrow).
    
End EscrowExtraction.

Module EscrowLiquidityExtraction.
  From ConCert.Extraction Require Import LPretty LiquidityExtract.
  (** A translation table for definitions we want to remap. The corresponding top-level definitions will be *ignored* *)

  
  Definition chainDef := "type chain = (nat * (nat * nat))".
  Definition storageDef := "type storage = state".
  Definition contractcallcontextDef := "type cctx = (timestamp * (address * (tez * tez)))".
  Notation "'msg'" := ((Msg * ContractCallContext) * Chain)%type.

  Definition liquidity_escrow_receive (m : msg) (s : State) := 
    match EscrowExtract.receive m.2 m.1.2 s (Some m.1.1) with
    | Some (s, acts) => Some (acts, s)
    | None => None
    end.
  
  Definition ESCROW_MODULE_LIQUIDITY : LiquidityMod msg ContractCallContext (Setup * Chain) State ActionBody :=
    {| (* a name for the definition with the extracted code *)
      lmd_module_name := "liquidity_escrow" ;

      (* definitions of operations on pairs and ints *)
      lmd_prelude := String.concat nl ([LiquidityPrelude; contractcallcontextDef; chainDef]);

      (* initial storage *)
      lmd_init := escrow_init_wrapper;

      lmd_init_prelude := 
           nl ++ "let evenTez (i : tez) = match i/2tz with | Some (_, r) -> r=0tz | None -> false in"
        ++ nl ++ "let eqTez (a : tez ) (b : tez ) = a = b in"
        ++ nl ++ "let eq_addr (a1 : address) (a2 : address) = a1 = a2 in"
        ++ nl ++ "let andb (a : bool ) (b : bool ) = a & b in"
        ++ nl;

      (* the main functionality *)
      lmd_receive := liquidity_escrow_receive ;

      (* code for the entry point *)
      lmd_entry_point :=   storageDef ++ nl 
                        ++ printWrapper (PREFIX ++ "liquidity_escrow_receive") ++ nl
                        ++ printMain |}.


 (** A translation table for definitions we want to remap. The corresponding top-level definitions will be *ignored* *)
  Definition TT_remap_liquidity : list (kername * string) :=
    [
      remap <%% Amount %%> "tez"
    ; remap <%% Nat.add %%> "addNat"
    ; remap <%% Nat.ltb %%> "ltNat"
    ; remap <%% Nat.mul %%> "multNat"
    ; remap <%% Z.add %%> "addTez"
    ; remap <%% Z.mul %%> "multTez"
    ; remap <%% Z.sub %%> "subTez"
    ; remap <%% Z.leb %%> "leTez"
    ; remap <%% Z.ltb %%> "ltTez"
    ; remap <%% Z.div %%> "divTez"
    ; remap <%% Z.even %%> "evenTez"
    ; remap <%% Z.eqb %%> "eqTez"
    ; remap <%% Z %%> "tez"

    ; remap <%% @ActionBody %%> "operation"
    ; remap <%% @ContractCallContext %%> "cctx"
    ; remap <%% @chain_height %%> "(fun (c : chain) -> c.(0))"
    ; remap <%% @current_slot %%> "(fun (c : chain) -> c.(1).(0))"
    ; remap <%% @finalized_height %%> "(fun (c : chain) -> c.(1).(1))"
    ; remap <%% @ctx_from %%> "(fun (c : cctx) -> c.(1).(0))"
    ; remap <%% @ctx_contract_address %%> "(fun (c : cctx) -> c.(0))"
    ; remap <%% @ctx_contract_balance %%> "(fun (c : cctx) -> c.(1).(1).(0))"
    ; remap <%% @ctx_amount %%> "(fun (c : cctx) -> c.(1).(1).(1))"
    ; remap <%% @address_eqb %%> "eq_addr"

    ; remap <%% _2 %%> "2p"
    ; remap <%% _3 %%> "3p"
    ; remap <%% _4 %%> "4p"
    ; remap <%% deadline %%> "50p"

    ; remap <%% @List.fold_left %%> "List.fold"
    ; remap <%% @List.map %%> "List.map"
    ; remap <%% @List.find %%> "List.find"
    ; remap <%% @List.length %%> "List.length"
    ; remap <%% @List.app %%> "List.append"
    ].
  (** A translation table of constructors and some constants. The corresponding definitions will be extracted and renamed. *)
  Definition TT_rename_liquidity : list (string * string):=

    [ ("Some", "Some")
    ; ("None", "None")
    ; ("Zpos" ,"int")
    ; ("Npos" ,"(fun (n:nat) -> n)")
    ; ("Zneg" ,"-")
    ; ("Z0" ,"0tz")
    ; ("N0" ,"0")
    ; ("xH" ,"0")
    ; ("1" ,"1")
    ; ("nil", "[]")
    ; ("true", "true")
    ; ("tt", "()")
    ].

  Definition to_inline : list kername := 
    [
      <%% Monads.Monad_option %%>
    ; <%% @Monads.bind %%>
    ; <%% @Monads.ret %%>
    ; <%% @Monads.lift %%>
    ; <%% bool_rect %%>
    ; <%% bool_rec %%>
    ; <%% option_map %%>
    ; <%% @Extras.with_default %%>

    (* necessary because liquidity doesn't allow calls to other functions in init for some reason *)
    ; <%% @EscrowExtract.init %%>

    ; <%% @setter_from_getter_State_last_action %%>
    ; <%% @setter_from_getter_State_next_step %%>
    ; <%% @setter_from_getter_State_seller %%>
    ; <%% @setter_from_getter_State_buyer %%>
    ; <%% @setter_from_getter_State_seller_withdrawable %%>
    ; <%% @setter_from_getter_State_buyer_withdrawable %%>

    ; <%% @set_State_last_action %%>
    ; <%% @set_State_next_step %%>
    ; <%% @set_State_seller %%>
    ; <%% @set_State_buyer %%>
    ; <%% @set_State_seller_withdrawable %%>
    ; <%% @set_State_buyer_withdrawable %%>

    ].
    
  Time MetaCoq Run
      (t <- liquidity_extraction_specialize PREFIX TT_remap_liquidity TT_rename_liquidity to_inline ESCROW_MODULE_LIQUIDITY ;;
        tmDefinition ESCROW_MODULE_LIQUIDITY.(lmd_module_name) t
      ).

  Print liquidity_escrow.

  (** We redirect the extraction result for later processing and compiling with the Liquidity compiler *)
  Redirect "examples/liquidity-extract/escrow.liq" MetaCoq Run (tmMsg liquidity_escrow).
  
End EscrowLiquidityExtraction.
(** * Extraction of a simple counter contract *)

From Coq Require Import PeanoNat ZArith Notations.

From MetaCoq.Template Require Import Loader.
From MetaCoq.Erasure Require Import Loader.

From ConCert.Embedding Require Import MyEnv CustomTactics.
From ConCert.Embedding Require Import Notations.
(* From ConCert.Embedding Require Import SimpleBlockchain. *)
From ConCert.Embedding.Extraction Require Import PreludeExt.
From ConCert.Extraction Require Import LPretty
     LiquidityExtract
     Common
     Optimize
     SpecializeChainBase.
From ConCert.Execution Require Import Automation.
From ConCert.Execution Require Import Serializable.
From ConCert.Execution Require Import Blockchain.
From ConCert.Execution Require Import EIP20Token.
From Coq Require Import List Ascii String.
Local Open Scope string_scope.

From MetaCoq.Template Require Import All.

Import ListNotations.
Import MonadNotation.

Open Scope Z.

Definition PREFIX := "".

Definition TT_remap_default : list (kername * string) :=
  [
    (* types *)
    remap <%% Z %%> "tez"
  ; remap <%% N %%> "int"
  ; remap <%% nat %%> "nat"
  ; remap <%% bool %%> "bool"
  ; remap <%% unit %%> "unit"
  ; remap <%% list %%> "list"
  ; remap <%% @fst %%> "fst"
  ; remap <%% @snd %%> "snd"
  ; remap <%% option %%> "option"
  ; remap <%% gmap.gmap %%> "map"
  ; remap <%% positive %%> "nat"
  ; remap <%% Amount %%> "tez"
  ; remap <%% @Address %%> "address"

  (* operations *)
  (* Note: N is mapped to Int instead of nat because Liquidity's minus operator on nats returns an int, 
     which is not compatible with N.sub since it returns an N *)
  ; remap <%% List.fold_left %%> "List.fold"
  ; remap <%% Pos.add %%> "addNat"
  ; remap <%% Pos.sub %%> "subNat"
  ; remap <%% Pos.leb %%> "leNat"
  ; remap <%% Pos.eqb %%> "eqNat"
  ; remap <%% Z.add %%> "addTez"
  ; remap <%% Z.sub %%> "subTez"
  ; remap <%% Z.leb %%> "leTez"
  ; remap <%% Z.ltb %%> "ltTez"
  ; remap <%% Z.eqb %%> "eqTez"
  ; remap <%% Z.gtb %%> "gtbTez"
  ; remap <%% N.add %%> "addInt"
  ; remap <%% N.sub %%> "subInt"
  ; remap <%% N.leb %%> "leInt"
  ; remap <%% N.ltb %%> "ltInt"
  ; remap <%% N.eqb %%> "eqInt"
  ; remap <%% andb %%> "andb"
  ; remap <%% negb %%> "not"
  ; remap <%% orb %%> "orb"
  ; remap <%% eqb_addr %%> "eq_addr"
  ].

From ConCert.Execution.Examples Require EIP20Token.

Section EIP20TokenExtraction.
  Import EIP20Token.
  From ConCert.Utils Require Import RecordUpdate.
  Import RecordSetNotations.
  Require Import Containers.
  From stdpp Require gmap.

  Notation params := (ContractCallContext × option EIP20Token.Msg).
  Open Scope N_scope.

    (* A specialized version of FMap's partial alter, w.r.t. FMap Address N *)
  Definition partial_alter_addr_int : string :=
       "let partial_alter_addr_int (f : int option -> int option)" ++ nl
    ++ "                           (k : address)" ++ nl
    ++ "                           (m : (address,int) map) : (address,int) map =" ++ nl
    ++ "  match Map.find k m with" ++ nl
    ++ "    Some v -> Map.update k (f (Some v)) m" ++ nl
    ++ "  | None -> Map.update k (f (None : int option)) m" ++ nl.

  Definition test_try_transfer (from : Address)
      (to_addr : Address)
      (amountt : TokenValue)
      (state : State) : option State :=
    let from_balance := Extras.with_default 0 (FMap.find from state.(balances)) in
    if from_balance <? amountt
    then None
    else let new_balances := FMap.add from (from_balance - amountt) state.(balances) in
        let new_balances := FMap.partial_alter (fun balance => Some (Extras.with_default 0 balance + amountt)) to_addr new_balances in
        Some ({|
          balances := new_balances;
          total_supply := state.(total_supply);
          allowances := state.(allowances);
        |}).

  Open Scope bool_scope.
  Definition test_try_transfer_from (delegate : Address)
      (from : Address)
      (to_addr : Address)
      (amountt : TokenValue)
      (state : State) : option State :=
  match FMap.find from state.(allowances) with
  | Some from_allowances_map =>
  match FMap.find delegate from_allowances_map with
  | Some delegate_allowance =>
  let from_balance := Extras.with_default 0 (FMap.find from state.(balances)) in
  if (delegate_allowance <? amountt) || (from_balance <? amountt)
  then None
  else let new_allowances := FMap.add delegate (delegate_allowance - amountt) from_allowances_map in
      let new_balances := FMap.add from (from_balance - amountt) state.(balances) in
      let new_balances := FMap.partial_alter (fun balance => Some (Extras.with_default 0 balance + amountt)) to_addr new_balances in
      Some ({|
        balances := new_balances;
        allowances := FMap.add from new_allowances state.(allowances);
        total_supply := state.(total_supply)|})
  | _ => None
  end
  | _ => None
  end.

  Definition test_init (ctx : ContractCallContext) (setup : EIP20Token.Setup) : option EIP20Token.State :=
    Some {| total_supply := setup.(init_amount);
            balances := FMap.empty;
            allowances := FMap.empty |}.

  Open Scope Z_scope.
  Definition test_receive
      (ctx : ContractCallContext)
      (state : EIP20Token.State)
      (maybe_msg : option EIP20Token.Msg)
    : option (list ActionBody * EIP20Token.State) :=
    let sender := ctx.(ctx_from) in
    let without_actions := option_map (fun new_state => ([], new_state)) in
    match maybe_msg with
    | Some (transfer to_addr amountt) => without_actions (test_try_transfer sender to_addr amountt state)
    | Some (transfer_from from to_addr amountt) => without_actions (test_try_transfer_from sender from to_addr amountt state)
    (* 'approve' endpoint not included in this test *)
    | _ => None
    end.

  Definition receive_wrapper
             (params : params)
             (st : State) : option (list ActionBody × State) :=
    test_receive params.1 st params.2.

  Definition init (ctx : ContractCallContext) (setup : EIP20Token.Setup) : option EIP20Token.State :=
    (* ensure extraction does not optimize unused ctx away *)
    let ctx_ := ctx in
    Some {| total_supply := setup.(init_amount);
            balances := FMap.add (EIP20Token.owner setup) (init_amount setup) FMap.empty;
            allowances := FMap.empty |}.
  Open Scope Z_scope.

  Definition EIP20Token_MODULE : LiquidityMod params ContractCallContext EIP20Token.Setup EIP20Token.State ActionBody :=
  {| (* a name for the definition with the extracted code *)
      lmd_module_name := "liquidity_eip20token" ;

      (* definitions of operations on pairs and ints *)
      lmd_prelude := LiquidityPrelude ++ nl 
                  ++ partial_alter_addr_int;

      (* initial storage *)
      lmd_init := init ;

      lmd_init_prelude := "type storage = state" ++ nl;

      (* the main functionality *)
      lmd_receive := receive_wrapper ;

      (* code for the entry point *)
      lmd_entry_point := printWrapper (PREFIX ++ "receive_wrapper") ++ nl
      ++ printMain |}.

  
  Definition TT_remap_eip20token : list (kername * string) :=
  TT_remap_default ++ [
    remap <%% @ContractCallContext %%> "(address * (address * int))"
  ; remap <%% @ctx_from %%> "fst" (* small hack, but valid since ContractCallContext is mapped to a tuple *)
  ; remap <%% @stdpp.base.partial_alter %%> "partial_alter_addr_int"
  ; remap <%% @stdpp.base.insert %%> "Map.add"
  ; remap <%% @fin_maps.map_insert %%> "Map.add"
  ; remap <%% @stdpp.base.Lookup %%> "Map.find"
  ; remap <%% @gmap.gmap_lookup %%> "Map.find"
  ; remap <%% @gmap.gmap_empty %%> "Map []"
  ; remap <%% @stdpp.base.empty %%> ""
  ; remap <%% @gmap.gmap_partial_alter %%> ""
  ; remap <%% @address_eqdec %%> ""
  ; remap <%% @address_countable %%> ""
  ].

  Definition TT_rename_eip20token :=
    [ ("Z0" ,"0tez")
    ; ("N0", "0")
    ; ("N1", "1")
    ; ("nil", "[]")
    ; ("tt", "()") ].

  Definition TT_inlines_eip20token : list kername := 
    [   
        <%% Monads.Monad_option %%>
      ; <%% bool_rect %%>
      ; <%% bool_rec %%>
      ; <%% option_map %%>
      ; <%% @Extras.with_default %%>

      ; <%% @stdpp.base.insert %%>
      ; <%% @stdpp.base.empty %%>
      ; <%% @stdpp.base.lookup %%>
    ].

  Time MetaCoq Run
      (t <- liquidity_extraction_specialize PREFIX TT_remap_eip20token TT_rename_eip20token TT_inlines_eip20token EIP20Token_MODULE ;;
      tmDefinition EIP20Token_MODULE.(lmd_module_name) t).

  Print liquidity_eip20token.

  (** We redirect the extraction result for later processing and compiling with the Liquidity compiler *)
  Redirect "./examples/liquidity-extract/liquidity_eip20token.liq" Compute liquidity_eip20token.


End EIP20TokenExtraction.

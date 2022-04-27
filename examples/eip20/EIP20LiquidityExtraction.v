(** * Extraction of a simple counter contract *)

From MetaCoq.Template Require Import All.
From ConCert.Embedding Require Import Notations.
From ConCert.Embedding.Extraction Require Import PreludeExt.
From ConCert.Extraction Require LPretty.
From ConCert.Extraction Require Import LiquidityExtract.
From ConCert.Extraction Require Import Common.
From ConCert.Execution Require Import Blockchain.
From ConCert.Examples.EIP20 Require EIP20Token.
From ConCert.Execution Require Import ContractCommon.
From Coq Require Import String.
From Coq Require Import ZArith.

Import MonadNotation.

Local Open Scope string_scope.

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

Section EIP20TokenExtraction.
  Import EIP20Token.

  Notation params := (ContractCallContext × option EIP20Token.Msg).
  Open Scope N_scope.
  Open Scope bool.

  (* We define a version of [receive] that has the right signature. *)
  (* TODO: remove, once the [LiquidityMod] is fixed. *)
  Definition test_receive
      (ctx : ContractCallContext)
      (state : EIP20Token.State)
      (maybe_msg : option EIP20Token.Msg)
    : option (list ActionBody * EIP20Token.State) :=
    let sender := ctx.(ctx_from) in
    let without_actions := option_map (fun new_state => ([], new_state)) in
    match maybe_msg with
    | Some (transfer to_addr amountt) => without_actions (try_transfer sender to_addr amountt state)
    | Some (transfer_from from to_addr amountt) => without_actions (try_transfer_from sender from to_addr amountt state)
   | Some (approve delegate amount) => without_actions (try_approve sender delegate amount state)
    | _ => None
    end.

  Definition receive_wrapper
             (params : params)
             (st : State) : option (list ActionBody × State) :=
    test_receive params.1 st params.2.

  (* The same as for [test_receive].
     TODO: remove, once the [LiquidityMod] is fixed. *)
  Definition init (ctx : ContractCallContext) (setup : EIP20Token.Setup) : option EIP20Token.State :=
    (* ensure extraction does not optimize unused ctx away
       NOTE: can be dealt with in a better way using the mask-override mechanism of dearging *)
    let ctx_ := ctx in
    Some {| total_supply := setup.(init_amount);
            balances := AddressMap.add (EIP20Token.owner setup) (init_amount setup) AddressMap.empty;
            allowances := AddressMap.empty |}.
  Open Scope Z_scope.

  Definition printERC20Wrapper (contract : string): string :=
  "let wrapper param (st : storage)"
        ++ " = "
        ++ "match " ++ contract ++ " (" ++ liquidity_call_ctx ++ ", param) st" ++ " with"
        ++ "| Some v -> v"
        ++ "| None -> failwith ()".

  Definition EIP20Token_MODULE : LiquidityMod params ContractCallContext EIP20Token.Setup EIP20Token.State ActionBody :=
  {| (* a name for the definition with the extracted code *)
      lmd_module_name := "liquidity_eip20token" ;

      (* definitions of operations on pairs and ints *)
      lmd_prelude := LPretty.LiquidityPrelude;


      (* initial storage *)
      lmd_init := init ;

      lmd_init_prelude := "";

      (* the main functionality *)
      lmd_receive := receive_wrapper ;

      (* code for the entry point *)
      lmd_entry_point := "type storage = state" ++ nl
                          ++ printERC20Wrapper (PREFIX ++ "receive_wrapper") ++ nl
      ++ LPretty.printMain |}.


  Definition TT_remap_eip20token : list (kername * string) :=
    TT_remap_default ++ [
    remap <%% @ContractCallContext %%> "(timestamp * (address * (tez * tez)))"
  ; remap <%% @ctx_from %%> "(fun x -> x.(1).(0))" (* small hack, but valid since ContractCallContext is mapped to a tuple *)
  ; remap <%% gmap.gmap %%> "map"
  ; remap <%% @AddressMap.add %%> "Map.add"
  ; remap <%% @AddressMap.find %%> "Map.find"
  ; remap <%% @AddressMap.empty %%> "(Map [])"
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
    ; <%% @Monads.bind %%>
    ; <%% @Monads.ret %%>
    ; <%% bool_rect %%>
    ; <%% bool_rec %%>
    ; <%% option_map %%>
    ; <%% @Extras.with_default %%>

    ; <%% @setter_from_getter_State_balances %%>
    ; <%% @setter_from_getter_State_total_supply %%>
    ; <%% @setter_from_getter_State_allowances %%>
    ; <%% @set_State_balances %%>
    ; <%% @set_State_allowances%%>

    ].

  Time MetaCoq Run
      (t <- liquidity_extraction_specialize PREFIX TT_remap_eip20token TT_rename_eip20token TT_inlines_eip20token EIP20Token_MODULE ;;
      tmDefinition EIP20Token_MODULE.(lmd_module_name) t).
  
  (** We redirect the extraction result for later processing and compiling with the Liquidity compiler *)
  Redirect "../extraction/tests/extracted-code/liquidity-extract/liquidity_eip20token.liq"
  Compute liquidity_eip20token.

End EIP20TokenExtraction.

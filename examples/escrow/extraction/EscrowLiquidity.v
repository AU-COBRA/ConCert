(** * Extraction of Escrow to CameLIGO and liquidity*)

From MetaCoq.Template Require Import All.
From ConCert.Embedding.Extraction Require Import SimpleBlockchainExt.
From ConCert.Execution Require Import Blockchain.
From ConCert.Execution Require Import ResultMonad.
From ConCert.Execution Require Monad.
From ConCert.Execution Require OptionMonad.
From ConCert.Examples.Escrow Require Import Escrow.
From ConCert.Extraction Require Import Common.
From ConCert.Extraction Require LiquidityPretty.
From ConCert.Extraction Require LiquidityExtract.
From Coq Require Import String.
From Coq Require Import ZArith_base.

Local Open Scope string_scope.

Definition escrow_init_wrapper (cctx : ContractCallContext)
                               (s : Setup * Chain)
                               : result State Error :=
  Escrow.init (snd s) cctx (fst s).

Definition escrow_receive (c : Chain)
                          (cctx : ContractCallContext)
                          (s : State)
                          (msg : option Msg)
                          : result (list ActionBody * State) Error :=
  match Escrow.receive c cctx s msg with
  | Ok (s, acts) => Ok (acts, s)
  | Err e => Err e
  end.

Module EscrowLiquidityExtraction.
  Definition PREFIX := "".

  Import LiquidityPretty.
  Import LiquidityExtract.
  (** A translation table for definitions we want to remap. The corresponding top-level definitions will be *ignored* *)


  Definition chainDef := "type chain = (nat * (nat * nat))".
  Definition storageDef := "type storage = state".
  Definition contractcallcontextDef := "type cctx = (timestamp * (address * (tez * tez)))".
  Notation "'msg'" := ((Msg * ContractCallContext) * Chain)%type.

  Definition liquidity_escrow_receive (m : msg) (s : State) :=
    match receive m.2 m.1.2 s (Some m.1.1) with
    | Ok (s, acts) => Ok (acts, s)
    | Err e => Err e
    end.

  Definition ESCROW_MODULE_LIQUIDITY : LiquidityMod msg ContractCallContext (Setup * Chain) State ActionBody Error :=
    {| (* a name for the definition with the extracted code *)
      lmd_module_name := "liquidity_escrow" ;

      (* definitions of operations on pairs and ints *)
      lmd_prelude := concat nl ([LiquidityPrelude; contractcallcontextDef; chainDef]);

      (* initial storage *)
      lmd_init := escrow_init_wrapper;

      lmd_init_prelude :=
           nl ++ "let evenTez (i : tez) = match i/2tz with | Some (_, r) -> r=0tz | None -> false in"
        ++ nl ++ "let eqTez (a : tez) (b : tez) = a = b in"
        ++ nl ++ "let eq_addr (a1 : address) (a2 : address) = a1 = a2 in"
        ++ nl ++ "let andb (a : bool) (b : bool) = a & b in"
        ++ nl ++ "let default_error = 1 in"
        ++ nl;

      (* the main functionality *)
      lmd_receive := liquidity_escrow_receive ;

      (* code for the entry point *)
      lmd_entry_point := storageDef ++ nl
                      ++ printWrapper (PREFIX ++ "liquidity_escrow_receive") ++ nl
                      ++ printMain
    |}.


 (** A translation table for definitions we want to remap. The corresponding top-level definitions will be *ignored* *)
  Definition TT_remap_liquidity : list (kername * string) :=
    [ remap <%% Amount %%> "tez"
    ; remap <%% Nat.add %%> "addNat"
    ; remap <%% Nat.ltb %%> "ltNat"
    ; remap <%% Nat.mul %%> "multNat"
    ; remap <%% Z.add %%> "addTez"
    ; remap <%% Z.mul %%> "multTez"
    ; remap <%% Z.sub %%> "subTez"
    ; remap <%% Z.leb %%> "leTez"
    ; remap <%% Z.ltb %%> "ltTez"
    ; remap <%% Z.gtb %%> "gtTez"
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

    ; remap <%% @List.fold_left %%> "List.fold"
    ; remap <%% @List.map %%> "List.map"
    ; remap <%% @List.find %%> "List.find"
    ; remap <%% @List.length %%> "List.length"
    ; remap <%% @List.app %%> "List.append"

    ; remap <%% ConCert.Execution.ResultMonad.result %%> "result"
    ].

  (** A translation table of constructors and some constants. The corresponding definitions will be extracted and renamed. *)
  Definition TT_rename_liquidity : list (string * string) :=
    [ ("Some", "Some")
    ; ("None", "None")
    ; ("Ok", "Ok")
    ; ("Err", "Err")
    ; ("Zpos" ,"int")
    ; ("Npos" ,"(fun (n:nat) -> n)")
    ; ("Zneg" ,"-")
    ; ("O", "0")
    ; ("Z0" ,"0tz")
    ; ("N0" ,"0")
    ; ("xH" ,"0")
    ; ("1" ,"1")
    ; ("nil", "[]")
    ; ("true", "true")
    ; ("tt", "()")
    ].

  Definition to_inline : list kername :=
    [ <%% OptionMonad.Monad_option %%>
    ; <%% @ConCert.Execution.ResultMonad.Monad_result %%>
    ; <%% @Monad.bind %%>
    ; <%% @Monad.ret %%>
    ; <%% @Monad.lift %%>
    ; <%% bool_rect %%>
    ; <%% bool_rec %%>
    ; <%% option_map %%>
    ; <%% @Extras.with_default %%>

    (* necessary because liquidity doesn't allow calls to other functions in init for some reason *)
    ; <%% @init %%>

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

  Import MCMonadNotation.

  Time MetaCoq Run
      (t <- liquidity_extraction_specialize PREFIX TT_remap_liquidity TT_rename_liquidity to_inline ESCROW_MODULE_LIQUIDITY ;;
        tmDefinition (String.of_string ESCROW_MODULE_LIQUIDITY.(lmd_module_name)) t
      ).

  (** We redirect the extraction result for later processing and compiling with the Liquidity compiler *)
  Redirect "../extraction/tests/extracted-code/liquidity-extract/escrow.liq"
  MetaCoq Run (tmMsg (String.of_string liquidity_escrow)).

End EscrowLiquidityExtraction.

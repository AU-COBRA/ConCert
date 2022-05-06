(** * Extraction of Escrow to CameLIGO and liquidity*)

From MetaCoq.Template Require Import All.
From ConCert.Embedding.Extraction Require Import SimpleBlockchainExt.
From ConCert.Execution Require Import Blockchain.
From ConCert.Examples.Escrow Require Import Escrow.
From ConCert.Extraction Require Import Common.
From ConCert.Extraction Require CameLIGOPretty.
From ConCert.Extraction Require CameLIGOExtract.
From ConCert.Extraction Require LPretty.
From ConCert.Extraction Require LiquidityExtract.
From Coq Require Import String.
From Coq Require Import ZArith.

Local Open Scope string_scope.

Definition escrow_init_wrapper (cctx : ContractCallContext) (s : Setup * Chain) : option State :=
    Escrow.init (snd s) cctx (fst s).

Definition ligo_init (s : Address * Setup * nat) : option State :=
  let seller := s.1.1 in
  let setup := s.1.2 in
  let curr_slot := s.2 in
  let buyer := setup_buyer setup in
  if (buyer =? seller)%address then None
  else Some {| last_action := curr_slot;
               next_step := buyer_commit;
               seller := seller;
               buyer := buyer;
               seller_withdrawable := 0;
               buyer_withdrawable := 0 |}.

Lemma escrow_init_eq_ligo_init cctx s :
  (* The contract should be deployed with non-zero even amount *)
  (ctx_amount cctx =? 0 = false)%Z ->
  Z.even (ctx_amount cctx) ->
  escrow_init_wrapper cctx s = ligo_init (cctx.(ctx_from),s.1, s.2.(current_slot)).
Proof.
  intros Hamount Heven.
  unfold escrow_init_wrapper,init, ligo_init. cbn.
  rewrite Hamount.
  now destruct (_ =? _)%address; destruct (Z.even _).
Qed.

Definition escrow_receive (c : Chain) (cctx : ContractCallContext) (s : State) (msg : option Msg) : option (list ActionBody * State) :=
    match Escrow.receive c cctx s msg with
    | Some (s, acts) => Some (acts, s)
    | None => None
    end.


Module EscrowCameLIGOExtraction.
  Import CameLIGOExtract.
  Import CameLIGOPretty.
  Existing Instance PrintConfShortNames.PrintWithShortNames.

  (** A translation table of constructors and some constants. The corresponding definitions will be extracted and renamed. *)
  Definition TT_rename_ligo : list (string * string):=
    [ ("true", "true")
    ; ("false", "false")
    ; ("tt", "()")
    ].

  Definition TT_remap_ligo : list (kername * string) := [ remap <%% subAmountOption %%> "subTez" ].
  
  Definition ESCROW_MODULE_LIGO : CameLIGOMod Msg ContractCallContext _ State ActionBody :=
    {| (* a name for the definition with the extracted code *)
      lmd_module_name := "cameligo_escrow" ;

      (* definitions of operations on numbers, call context, etc. *)
      lmd_prelude := CameLIGOPrelude;

      (* initial storage *)
      lmd_init := ligo_init ;

      (* no extra operations in [init] are required *)
      lmd_init_prelude := "";

      (* the main functionality *)
      lmd_receive := escrow_receive ;

      lmd_receive_prelude := "";
      (* code for the entry point *)
      lmd_entry_point :=
        printMain "escrow_receive" "msg" "state" 
    |}.

  Definition to_inline : list kername := 
    [ <%% Monads.Monad_option %%>
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
    ].

  Time MetaCoq Run
  (CameLIGO_prepare_extraction to_inline TT_remap_ligo TT_rename_ligo [] "cctx_instance" ESCROW_MODULE_LIGO).

  Time Definition cameLIGO_escrow := Eval vm_compute in cameligo_escrow_prepared.

  Redirect "../extraction/tests/extracted-code/cameligo-extract/EscrowExtract.mligo"
  MetaCoq Run (tmMsg cameLIGO_escrow).

End EscrowCameLIGOExtraction.

Module EscrowLiquidityExtraction.
  Definition PREFIX := "".
  
  Import LPretty.
  Import LiquidityExtract.
  (** A translation table for definitions we want to remap. The corresponding top-level definitions will be *ignored* *)

  
  Definition chainDef := "type chain = (nat * (nat * nat))".
  Definition storageDef := "type storage = state".
  Definition contractcallcontextDef := "type cctx = (timestamp * (address * (tez * tez)))".
  Notation "'msg'" := ((Msg * ContractCallContext) * Chain)%type.

  Definition liquidity_escrow_receive (m : msg) (s : State) := 
    match receive m.2 m.1.2 s (Some m.1.1) with
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

  Import MonadNotation.
  
  Time MetaCoq Run
      (t <- liquidity_extraction_specialize PREFIX TT_remap_liquidity TT_rename_liquidity to_inline ESCROW_MODULE_LIQUIDITY ;;
        tmDefinition ESCROW_MODULE_LIQUIDITY.(lmd_module_name) t
      ).

  (* (** we redirect the extraction result for later processing and compiling with the Liquidity compiler *) *)
  Redirect "../extraction/tests/extracted-code/liquidity-extract/escrow.liq"
  MetaCoq Run (tmMsg liquidity_escrow).

End EscrowLiquidityExtraction.

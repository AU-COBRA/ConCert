(** Extraction of Dexter 2 to CameLIGO *)

From Coq Require Import List.
From Coq Require Import String.
From Coq Require Import ZArith.
From MetaCoq.Template Require Import All.
From ConCert.Extraction Require Import Common.
From ConCert.Extraction Require Import CameLIGOPretty.
From ConCert.Extraction Require Import CameLIGOExtract.
From ConCert.Execution Require Import Serializable.
From ConCert.Execution Require Import Blockchain.
From ConCert.Execution Require Import Containers.
From ConCert.Execution Require ContractCommon.
From ConCert.Examples.Dexter2 Require Dexter2CPMM.
From ConCert.Examples.Dexter2 Require Dexter2FA12.
From ConCert.Utils Require Import RecordUpdate.
From ConCert.Utils Require Import StringExtra.

Local Open Scope string_scope.

(** Printing configuration *)

(** We print long names for data types and constructors to avoid clashes, but keep constants' names short (no module name added) *)
Instance dexter2_print_config : CameLIGOPrintConfig :=
  {| print_ctor_name := PrintConfAddModuleNames.print_ctor_name_;
     print_type_name := PrintConfAddModuleNames.print_ind_type_name_;
     print_const_name := snd |}.

(** * Common extraction setup *)

Definition call_to_token_ligo : string :=
  <$ "let call_to_token (type msg) (addr : address) (amt : nat) (msg : msg) : operation =" ;
     "  let token_ : msg contract =";
     "  match (Tezos.get_contract_opt (addr) : msg contract option) with";
     "    Some contract -> contract";
     "  | None -> (failwith ""Contract not found."" : msg contract) in";
     "  Tezos.transaction msg (natural_to_mutez amt) token_" $>.

Definition mk_callback_ligo : string :=
  "[@inline] let mk_callback (type msg)(addr : address) (msg : msg) : operation = call_to_token addr 0n msg".

(** Next two definition are borrowed from the actual Dexter 2 implementation
     https://gitlab.com/dexter2tz/dexter2tz/-/blob/1cec9d9333eba756603d6cd90ea9c70d482a5d3d/dexter.mligo *)
Definition natural_to_mutez_ligo : string :=
  "[@inline] let natural_to_mutez (a: nat): tez = a * 1mutez".

Definition mutez_to_natural_ligo : string :=
  "[@inline] let mutez_to_natural (a: tez): nat = a / 1mutez".

(** We change the signature of the original definition slightly, so it takes a [nat] and converts
    in to [tez]. We also return [operation option] instead of failing *)
Definition xtz_transfer_ligo : string :=
  <$ "let xtz_transfer (to_ : address) (amount_ : nat) : operation option =";
     "  match (Tezos.get_contract_opt to_ : unit contract option) with";
     "    | None -> None";
     "    | Some c -> Some (Tezos.transaction () (natural_to_mutez amount_) c)" $>.

Definition subNatTruncated_ligo : string :=
  "let subNTruncated (n : nat) (m : nat) : nat = if n < m then 0n else abs (n-m)".

Definition edivNatTrancated_ligo : string :=
  "let edivTruncated (a : nat) (b : nat) = match ediv a b with Some v -> v | None -> (0n,0n)".

(** Remapping arithmetic operations. *)
(** We override the default remappings of aritmetic operations since it remaps [Z] to
    [tez], and [N] to [int], which is not sutable for our purposes. *)
Definition TT_remap_arith : list (kername * string) :=
[   remap <%% Z %%> "int"
  ; remap <%% N %%> "nat"

  ; remap <%% N.add %%> "addN"
  ; remap <%% N.sub %%> "subNTruncated"
  ; remap <%% N.mul %%> "multN"
  ; remap <%% N.leb %%> "lebN"
  ; remap <%% N.ltb %%> "ltbN"
  ; remap <%% N.eqb %%> "eqN"
  ; remap <%% N.modulo %%> "moduloN"

  ; remap <%% Z.add %%> "addInt"
  ; remap <%% Z.sub %%> "subInt"
  ; remap <%% Z.mul %%> "multInt"
  ; remap <%% Z.leb %%> "leInt"
  ; remap <%% Z.ltb %%> "ltInt"
  ; remap <%% Z.eqb %%> "eqInt"
  ; remap <%% Z.gtb %%> "gtbInt"
  ; remap <%% Z.even %%> "evenInt"
  ; remap <%% Z.abs_N %%> "abs"

  ; remap <%% Z.of_N %%> "z_of_N"
  ; remap <%% Z.to_N %%> "abs"
].

(** Remapping key-value maps *)
Definition TT_remap_dexter2 : list (kername * string) :=
   [
    remap <%% @ContractCallContext %%> CameLIGO_call_ctx_type_name
  ; remap <%% @FMap %%> "map"
  ; remap <%% @ContractCommon.AddressMap.add %%> "Map.add"
  ; remap <%% @ContractCommon.AddressMap.find %%> "Map.find_opt"
  ; remap <%% @ContractCommon.AddressMap.empty %%> "Map.empty"
  ; remap <%% @ContractCommon.AddressMap.update %%> "Map.update"
  ; remap <%% @FMap.add %%> "Map.add"
  ; remap <%% @FMap.find %%> "Map.find_opt"
  ; remap <%% @FMap.empty %%> "Map.empty"
  ; remap <%% @FMap.update %%> "Map.update"
  ; remap <%% @address_eqb %%> "eq_addr"
   ].

(** Definitions to inline *)
Definition TT_inlines_dexter2 : list kername :=
    [
      <%% Monads.Monad_option %%>
    ; <%% @Monads.bind %%>
    ; <%% @Monads.ret %%>
    ; <%% @Extras.with_default %%>
    ; <%% option_map %%>

    ; <%% @SetterFromGetter %%>
    ; <%% @Dexter2CPMM.setter_from_getter_State_tokenPool %%>
    ; <%% @Dexter2CPMM.setter_from_getter_State_selfIsUpdatingTokenPool %%>
    ; <%% @Dexter2CPMM.setter_from_getter_State_xtzPool %%>
    ; <%% @Dexter2CPMM.setter_from_getter_State_lqtTotal %%>
    ; <%% @Dexter2CPMM.setter_from_getter_State_freezeBaker %%>
    ; <%% @Dexter2CPMM.setter_from_getter_State_manager %%>
    ; <%% @Dexter2CPMM.setter_from_getter_State_lqtAddress %%> ].


(** * Extracting Liquidity Token *)

Module Dexter2LqtExtraction.

  (** Serialisation plays no role in the extraction result, therfore we defining instances
      using the opaque ascription of module types to speedup the extraction *)
  Module DLqtSInstancesOpaque : Dexter2FA12.Dexter2LqtSerializable := Dexter2FA12.D2LqtSInstances.

  Module DEX2LQTExtract := Dexter2FA12.Dexter2Lqt DLqtSInstancesOpaque.

  Open Scope Z_scope.

  Import DEX2LQTExtract.
  Import Dexter2FA12.

  Section D2LqtE.
  Context `{ChainBase}.


  Definition extra_ignore :=
    [ <%% @Serializable %%>
    ; <%% @DLqtSInstancesOpaque.setup_serializable %%>
    ; <%% unit_serializable %%> ].

  Definition TT_Dexter2_Lqt :=
    [ remap <%% @mk_callback %%> "mk_callback"
    ; remap <%% non_zero_amount %%> "(fun (x : tez) -> 0tez < x)"
    ; remap <%% @update_allowance %%> "Map.update"
    ; remap <%% @find_allowance %%> "Map.find_opt"
    ; remap <%% @empty_allowance %%> "Map.empty"
     ].

  (** We redefine the init function, because in the Tezos blockchain
      there is no concept of initialisation function. However, it's common
      to provide a function that computes a valid initial storage that can
      be used for deployment. *)
  Definition init (setup : Setup) : option State :=
    Some {|
        tokens := ContractCommon.AddressMap.add setup.(lqt_provider) setup.(initial_pool) ContractCommon.AddressMap.empty;
        allowances := empty_allowance;
        admin := setup.(admin_);
        total_supply := setup.(initial_pool);
      |}.

    (** We prove that the "new" init function, which does not use [chain] and [ctx],
        computes the same result as the contract's init *)
  Lemma init_total_no_context_use chain ctx setup :
    Dexter2FA12.DEX2LQT.init_lqt chain ctx setup = init setup.
  Proof. reflexivity. Qed.

  Definition receive_ (chain : Chain)
       (ctx : ContractCallContext)
       (state : State)
       (maybe_msg : option Dexter2FA12.Msg)
    : option (list ActionBody * State) :=
    match DEX2LQTExtract.receive_lqt chain ctx state maybe_msg with
    | Some x => Some (x.2, x.1)
    | None => None
    end.

  Definition TT_remap_all :=
    (TT_remap_arith ++ TT_remap_dexter2 ++ TT_Dexter2_Lqt)%list.

  Definition LIGO_DEXTER2LQT_MODULE : CameLIGOMod Msg ContractCallContext Setup State ActionBody :=
  {| (* a name for the definition with the extracted code *)
     lmd_module_name := "cameLIGO_dexter2lqt" ;

      (* definitions of operations on pairs and ints *)
     lmd_prelude := CameLIGOPrelude ++ nl ++ nl ++
                    <$ call_to_token_ligo;
                       "";
                       mk_callback_ligo;
                       "";
                       natural_to_mutez_ligo;
                       "";
                       mutez_to_natural_ligo;
                       "";
                       xtz_transfer_ligo;
                       "";
                       subNatTruncated_ligo $>;

      (* initial storage *)
      lmd_init := init ;

      (* NOTE: printed as local [let]-bound definitions in the init *)
      lmd_init_prelude := "";

      (* TODO: maybe not needed, [lmd_prelude] should be enough *)
      lmd_receive_prelude := "";

      (* the main functionality *)
      lmd_receive := receive_ ;

      (* code for the entry point *)
    lmd_entry_point := print_default_entry_point <%% @State %%>
                                                 <%% @receive_ %%>
                                                 <%% @Msg %%> |}.

  Time MetaCoq Run
  (CameLIGO_prepare_extraction TT_inlines_dexter2 TT_remap_all TT_rename_ctors_default extra_ignore "cctx_instance" LIGO_DEXTER2LQT_MODULE).

  Time Definition cameLIGO_dexter2lqt := Eval vm_compute in cameLIGO_dexter2lqt_prepared.

  MetaCoq Run (tmMsg cameLIGO_dexter2lqt).

  (** We redirect the extraction result for later processing and compiling with the CameLIGO compiler *)
  Redirect "../extraction/tests/extracted-code/cameligo-extract/dexter2fa12.mligo"
           MetaCoq Run (tmMsg cameLIGO_dexter2lqt).

  End D2LqtE.
End Dexter2LqtExtraction.


(** * Extracting the Main Contract *)
Module Dexter2Extraction.

(** Serialisation plays no role in the extraction result, therfore we defining instances
    using the opaque ascription of module types to speedup the extraction *)
Module DSInstancesOpaque : Dexter2CPMM.Dexter2Serializable := Dexter2CPMM.DSInstances.

Module DEX2Extract := Dexter2CPMM.Dexter2 DSInstancesOpaque Dexter2CPMM.NullAddressAxiom.

Open Scope Z_scope.

Import DEX2Extract.
Import Dexter2CPMM.

Section D2E.
  Existing Instance BaseTypes.

  Definition extra_ignore :=
   [ <%% @Serializable %%>
   ; <%% @DSInstancesOpaque.DexterMsg_serializable %%> ].


  Definition TT_Dexter2_CPMM :=
   [ remap <%% @call_to_token %%> "call_to_token"
   ; remap <%% @call_to_other_token %%> "call_to_token"
   ; remap <%% @xtz_transfer %%> "xtz_transfer"
   ; remap <%% @call_liquidity_token %%> "call_to_token"
   ; remap <%% token_id %%> "nat"

   ; remap <%% @null_address %%> "(""tz1Ke2h7sDdakHJQh8WX4Z372du1KChsksyU"" : address)"

   ; remap <%% N_to_amount %%> "natural_to_mutez"
   ; remap <%% amount_to_N %%> "mutez_to_natural"
   ; remap <%% div %%> "divN_opt"
   ; remap <%% non_zero_amount %%> "(fun (x : tez) -> 0tez < x)"
   ; remap <%% @baker_address %%> "key_hash option"
   ; remap <%% set_delegate_call %%> "(fun (x : key_hash option) -> [Tezos.set_delegate x])" ].

  Definition TT_remap_all :=
    (TT_remap_arith ++ TT_remap_dexter2 ++ TT_Dexter2_CPMM)%list.

  (** We redefine [init] for the same reasons as for the liquidity token *)
  Definition init (setup : Setup) : option State :=
    Some {|
        tokenPool := 0;
        xtzPool := 0;
        lqtTotal := setup.(lqtTotal_);
        selfIsUpdatingTokenPool := false;
        freezeBaker := false;
        manager := setup.(manager_);
        tokenAddress := setup.(tokenAddress_);
        tokenId := setup.(tokenId_);
        lqtAddress := null_address
      |}.

  (** We prove that the "new" init function, which does not use [chain] and [ctx],
      is total and computes the same result as the contract's init *)
  Lemma init_total_no_context_use chain ctx setup :
    Dexter2CPMM.DEX2.init_cpmm chain ctx setup = init setup.
  Proof. reflexivity. Qed.


  Definition receive_ (chain : Chain)
       (ctx : ContractCallContext)
       (state : State)
       (maybe_msg : option Dexter2CPMM.Msg)
    : option (list ActionBody * State) :=
    match DEX2Extract.receive_cpmm chain ctx state maybe_msg with
    | Some x => Some (x.2, x.1)
    | None => None
    end.

  Definition LIGO_DEXTER2_MODULE : CameLIGOMod Msg ContractCallContext Setup State ActionBody :=
  {| (* a name for the definition with the extracted code *)
     lmd_module_name := "cameLIGO_dexter2" ;

      (* definitions of operations on pairs and ints *)
     lmd_prelude := CameLIGOPrelude ++ nl ++ nl ++
                    <$ call_to_token_ligo;
                       "";
                       natural_to_mutez_ligo;
                       "";
                       mutez_to_natural_ligo;
                       "";
                       xtz_transfer_ligo;
                       "";
                       subNatTruncated_ligo $>;

      (* initial storage *)
      lmd_init := init ;

      (* NOTE: printed as local [let]-bound definitions in the init *)
      lmd_init_prelude := "";

      (* TODO: maybe not needed, [lmd_prelude] should be enough *)
      lmd_receive_prelude := "";

      (* the main functionality *)
      lmd_receive := receive_ ;

      (* code for the entry point *)
    lmd_entry_point := print_default_entry_point <%% @State %%>
                                                 <%% @receive_ %%>
                                                 <%% @Msg %%> |}.

  Time MetaCoq Run
  (CameLIGO_prepare_extraction TT_inlines_dexter2 TT_remap_all TT_rename_ctors_default extra_ignore "cctx_instance" LIGO_DEXTER2_MODULE).

  Time Definition cameLIGO_dexter2 := Eval vm_compute in cameLIGO_dexter2_prepared.

  MetaCoq Run (tmMsg cameLIGO_dexter2).

  (** We redirect the extraction result for later processing and compiling with the CameLIGO compiler *)
  Redirect "../extraction/tests/extracted-code/cameligo-extract/dexter2CertifiedExtraction.mligo"
           MetaCoq Run (tmMsg cameLIGO_dexter2).

End D2E.
End Dexter2Extraction.

(** * Extraction of Dexter 2 to CameLIGO *)

From Coq Require Import PeanoNat ZArith Notations.
From Coq Require Import List Ascii String Bool.

From MetaCoq.Template Require Import All.

From ConCert.Embedding Require Import Notations.
From ConCert.Embedding Require Import MyEnv CustomTactics.
From ConCert.Embedding Require Import Notations.
From ConCert.Extraction Require Import Common Optimize.
From ConCert.Extraction Require Import CameLIGOPretty CameLIGOExtract.
From ConCert.Execution Require Import Serializable.
From ConCert.Execution Require Import Blockchain.
From ConCert.Execution.Examples Require Dexter2CPMM.
From ConCert.Execution Require Import Containers.
From ConCert.Utils Require Import RecordUpdate.
From ConCert.Utils Require Import StringExtra.

From stdpp Require gmap.


Local Open Scope string_scope.

Import MonadNotation.
Open Scope Z.

(** Exposing a printing configuration *)
Existing Instance PrintConfAddModuleNames.PrintWithModuleNames.

Import RecordSetNotations.


(** Serialisation plays no role in the extraction result, therfore we defining instances
    using the opaque ascription of module types to speedup the extraction *)
Module DSInstancesOpaque : Dexter2CPMM.Dexter2Serializable := Dexter2CPMM.DSInstances.

Module DEX2Extract := Dexter2CPMM.Dexter2 DSInstancesOpaque.

Section Dexter2Extraction.

  Context `{ChainBase}.

  Open Scope Z_scope.

  Import DEX2Extract.
  Import Dexter2CPMM.

  Definition init (ctx : ContractCallContext) (setup : Setup) : option State :=
    let ctx_ := ctx in
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

  Set Printing All.

  Print DEX2Extract.call_to_token.
  Definition receive_ (chain : Chain)
       (ctx : ContractCallContext)
       (state : State)
       (maybe_msg : option DEX2Extract.Msg)
    : option (list ActionBody * State) :=
    match DEX2Extract.receive chain ctx state maybe_msg with
    | Some x => Some (x.2, x.1)
    | None => None
    end.
  Close Scope Z_scope.

  Definition call_to_token_ligo : string :=
    <$ "let call_to_token (addr : address) (amt : nat) (msg : _msg) : operation =" ;
       "  let token_ : _msg contract =";
       "  match (Tezos.get_contract_opt (addr) : _msg contract option) with";
       "    Some contract -> contract";
       "  | None -> (failwith ""Contract not found."" : _msg contract) in";
       "  Tezos.transaction msg (natural_to_mutez amt) token_" $>.

  (** Next two definition are borrowed from the actual Dexter 2 implementation
       https://gitlab.com/dexter2tz/dexter2tz/-/blob/master/dexter.mligo *)
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

  Definition TT_remap_arith : list (kername * string) :=
[   remap <%% Z %%> "int"
  ; remap <%% N %%> "nat"
  ; remap <%% nat %%> "nat"

  ; remap <%% Nat.add %%> "addN"
  ; remap <%% Nat.leb %%> "lebN"
  ; remap <%% Nat.ltb %%> "ltbN"
  ; remap <%% Nat.mul %%> "multN"

  ; remap <%% Pos.add %%> "addN"
  ; remap <%% Pos.sub %%> "subN"
  ; remap <%% Pos.mul %%> "multN"
  ; remap <%% Pos.leb %%> "leN"
  ; remap <%% Pos.eqb %%> "eqN"
  ; remap <%% Z.add %%> "addInt"
  ; remap <%% Z.sub %%> "subInt"
  ; remap <%% Z.mul %%> "multInt"
  ; remap <%% Z.div %%> "divInt"
  ; remap <%% Z.leb %%> "leInt"
  ; remap <%% Z.ltb %%> "ltInt"
  ; remap <%% Z.eqb %%> "eqInt"
  ; remap <%% Z.gtb %%> "gtbInt"
  ; remap <%% Z.even %%> "evenInt"
  ; remap <%% N.add %%> "addN"
  ; remap <%% N.sub %%> "subNTruncated"
  ; remap <%% N.mul %%> "multN"
  ; remap <%% N.leb %%> "lebN"
  ; remap <%% N.ltb %%> "ltbN"
  ; remap <%% N.eqb %%> "eqN"
  ; remap <%% div %%> "divN_opt"
  ; remap <%% N.modulo %%> "moduloN"
  ; remap <%% N.sub %%> "subOption"
  ; remap <%% N_to_amount %%> "natural_to_mutez"
  ; remap <%% amount_to_N %%> "mutez_to_natural"
  ; remap <%% Z.of_N %%> "z_of_N"
  ; remap <%% non_zero_amount %%> "(fun (x : tez) -> 0tez < x)"
].

  Definition TT_remap_dexter2 : list (kername * string) :=
   [
    remap <%% @ContractCallContext %%> CameLIGO_call_ctx_type_name
  ; remap <%% @FMap %%> "map"
  ; remap <%% @Common.AddressMap.add %%> "Map.add"
  ; remap <%% @Common.AddressMap.find %%> "Map.find_opt"
  ; remap <%% @Common.AddressMap.empty %%> "Map.empty"
  ; remap <%% @FMap.add %%> "Map.add"
  ; remap <%% @FMap.find %%> "Map.find_opt"
  ; remap <%% @FMap.empty %%> "Map.empty"

  ; remap <%% @call_to_token %%> "call_to_token"
  ; remap <%% @call_to_other_token %%> "call_to_token"
  ; remap <%% @xtz_transfer %%> "xtz_transfer"
  ; remap <%% @call_liquidity_token %%> "call_to_token"
  ; remap <%% token_id %%> "nat"

  ; remap <%% @null_address %%> "(""tz1Ke2h7sDdakHJQh8WX4Z372du1KChsksyU"" : address)"
  ; remap <%% @Serializable %%> "" (* FIXME: workaround; should be ignored instead *)
  ; remap <%% @DSInstancesOpaque.DexterMsg_serializable %%> "" (* FIXME: workaround; should be ignored instead *)
   ].

  Definition TT_remap_all :=
    (TT_remap_arith ++ TT_remap_dexter2)%list.

  Definition TT_inlines_dexter2 : list kername :=
    [
      <%% Monads.Monad_option %%>
    ; <%% @Monads.bind %%>
    ; <%% @Monads.ret %%>
    ; <%% @Extras.with_default %%>

    ; <%% @SetterFromGetter %%> ].

  Time MetaCoq Run
  (CameLIGO_prepare_extraction TT_inlines_dexter2 TT_remap_all TT_rename_ctors_default "cctx_instance" LIGO_DEXTER2_MODULE).

  Time Definition cameLIGO_dexter2 := Eval vm_compute in cameLIGO_dexter2_prepared.

  MetaCoq Run (tmMsg cameLIGO_dexter2).

  (** We redirect the extraction result for later processing and compiling with the CameLIGO compiler *)
  Redirect "examples/extracted-code/cameligo-extract/dexter2CertifiedExtraction.mligo"
  MetaCoq Run (tmMsg cameLIGO_dexter2).

End Dexter2Extraction.

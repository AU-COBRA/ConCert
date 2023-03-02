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
From ConCert.Execution Require Import ResultMonad.
From ConCert.Examples.Dexter2 Require Import Dexter2CommonExtract.
From ConCert.Examples.Dexter2 Require Dexter2CPMM.
From ConCert.Utils Require Import StringExtra.

Local Open Scope string_scope.



(** * Extracting the Main Contract *)
Module Dexter2Extraction.

  (** Serialization plays no role in the extraction result. Therefore, we define instances
      using the opaque ascription of module types to speed up the extraction *)
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
    ; remap <%% div %%> "divN_res"
    ; remap <%% non_zero_amount %%> "(fun (x : tez) -> 0tez < x)"
    ; remap <%% @baker_address %%> "key_hash option"
    ; remap <%% set_delegate_call %%> "(fun (x : key_hash option) -> [Tezos.set_delegate x])" ].

    Definition TT_remap_all :=
      (TT_remap_dexter2_arith ++ TT_remap_dexter2 ++ TT_Dexter2_CPMM)%list.

    (** We redefine [init] for the same reasons as for the liquidity token *)
    Definition init (setup : Setup) : result State Error :=
      Ok {|
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
                        : result (list ActionBody * State) Error :=
      match DEX2Extract.receive_cpmm chain ctx state maybe_msg with
      | Ok x => Ok (x.2, x.1)
      | Err e => Err e
      end.

    Definition LIGO_DEXTER2_MODULE : CameLIGOMod Msg ContractCallContext Setup State ActionBody Error :=
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
                        subNatTruncated_ligo;
                        "";
                        divN_res_ligo $>;

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
                                                   <%% @Msg %%>
    |}.

    Time MetaCoq Run
      (CameLIGO_prepare_extraction TT_inlines_dexter2 TT_remap_all
        TT_rename_ctors_default extra_ignore "cctx_instance" LIGO_DEXTER2_MODULE).

    Time Definition cameLIGO_dexter2 := Eval vm_compute in cameLIGO_dexter2_prepared.

    (** We redirect the extraction result for later processing and compiling with the CameLIGO compiler *)
    Redirect "../extraction/tests/extracted-code/cameligo-extract/dexter2CertifiedExtraction.mligo"
      MetaCoq Run (tmMsg (s_to_bs cameLIGO_dexter2)).

  End D2E.
End Dexter2Extraction.

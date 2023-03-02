(** Extraction of Dexter 2 to CameLIGO *)

From Coq Require Import List.
From Coq Require Import String.
From MetaCoq.Template Require Import All.
From ConCert.Extraction Require Import Common.
From ConCert.Extraction Require Import CameLIGOPretty.
From ConCert.Extraction Require Import CameLIGOExtract.
From ConCert.Execution Require Import Serializable.
From ConCert.Execution Require Import Blockchain.
From ConCert.Execution Require Import ResultMonad.
From ConCert.Examples.Dexter2 Require Dexter2FA12.
From ConCert.Examples.Dexter2 Require Import Dexter2CommonExtract.
From ConCert.Utils Require Import StringExtra.

Local Open Scope string_scope.



(** * Extracting Liquidity Token *)

Module Dexter2LqtExtraction.

  (** Serialization plays no role in the extraction result. Therefore, we define instances
      using the opaque ascription of module types to speed up the extraction *)
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
        there is no concept of initialization function. However, it's common
        to provide a function that computes a valid initial storage that can
        be used for deployment. *)
    Definition init (setup : Setup) : result State Error :=
      Ok {|
          tokens := ContractCommon.AddressMap.add setup.(lqt_provider)
                                                  setup.(initial_pool)
                                                  ContractCommon.AddressMap.empty;
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
      : result (list ActionBody * State) Error :=
      match DEX2LQTExtract.receive_lqt chain ctx state maybe_msg with
      | Ok x => Ok (x.2, x.1)
      | Err e => Err e
      end.

    Definition TT_remap_all :=
      (TT_remap_dexter2_arith ++ TT_remap_dexter2 ++ TT_Dexter2_Lqt)%list.

    Definition LIGO_DEXTER2LQT_MODULE : CameLIGOMod Msg ContractCallContext Setup State ActionBody Error :=
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
                                                   <%% @Msg %%>
    |}.

    Time MetaCoq Run
      (CameLIGO_prepare_extraction TT_inlines_dexter2 TT_remap_all
        TT_rename_ctors_default extra_ignore "cctx_instance" LIGO_DEXTER2LQT_MODULE).

    Time Definition cameLIGO_dexter2lqt := Eval vm_compute in cameLIGO_dexter2lqt_prepared.

    (** We redirect the extraction result for later processing and compiling with the CameLIGO compiler *)
    Redirect "../extraction/tests/extracted-code/cameligo-extract/dexter2fa12.mligo"
      MetaCoq Run (tmMsg (s_to_bs cameLIGO_dexter2lqt)).

  End D2LqtE.
End Dexter2LqtExtraction.

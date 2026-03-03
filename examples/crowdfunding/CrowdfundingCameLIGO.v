(** * Extraction of various contracts to CameLIGO *)

From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From MetaRocq.Template Require Import All.
From ConCert.Embedding Require Import Notations.
From ConCert.Embedding.Extraction Require Import PreludeExt.
From ConCert.Embedding.Extraction Require SimpleBlockchainExt.
From ConCert.Examples.Crowdfunding Require Import CrowdfundingExt.
From ConCert.Examples.Crowdfunding Require CrowdfundingDataExt.
From ConCert.Extraction Require Import Common.
From ConCert.Extraction Require Import CameLIGOPretty.
From ConCert.Extraction Require Import CameLIGOExtract.
From ConCert.Execution Require Import Blockchain.
From ConCert.Execution Require Import ResultMonad.

Import MRMonadNotation.

Open Scope Z.


#[local]
Existing Instance PrintConfShortNames.PrintWithShortNames.

Module Crowdfunding.

  Notation storage := ((time_rocq × Z × address_rocq) × Maps.addr_map_rocq × bool).

  Definition crowdfunding_init (ctx : ContractCallContext)
                               (setup : (time_rocq × Z × address_rocq))
                               : result storage nat :=
      if ctx.(ctx_amount) =? 0 then Ok (setup, (Maps.mnil, false)) else Err 0%nat.

  Definition init (setup : (time_rocq × Z × address_rocq))
                  : result storage nat :=
    Ok (setup, (Maps.mnil, false)).

  Lemma crowdfunding_init_eq_init ctx setup :
    ctx.(ctx_amount) =? 0 -> (* no money should be sent on deployment *)
    crowdfunding_init ctx setup = init setup.
  Proof.
    intros Hamount.
    unfold crowdfunding_init.
    now rewrite Hamount.
  Qed.

  Open Scope Z.
  Import SimpleBlockchainExt.AcornBlockchain.
  Import CrowdfundingDataExt.
  Import CrowdfundingContract.Receive.

  (* We assume that there is a function converting addresses to [nat] *)
  Parameter addr_to_nat : forall `{ChainBase}, Blockchain.Address -> nat.

  Definition to_simple_ctx_addr `{ChainBase} (addr : Blockchain.Address) : address_rocq :=
    if address_is_contract addr then ContractAddr_rocq (addr_to_nat addr) else
      UserAddr_rocq (addr_to_nat addr).

  Definition crowdfunding_receive_inner
            (c : Chain)
            (ctx : ContractCallContext)
            (params : msg_rocq)
            (st : storage)
            : result (list SimpleActionBody_rocq × storage) nat :=
    let res := receive params st
            (Time_rocq c.(current_slot),
             (to_simple_ctx_addr ctx.(ctx_from),
             (ctx.(ctx_amount),
             ctx.(ctx_contract_balance)))) in
      result_of_option res 0%nat.

  Definition crowdfunding_receive (c : Chain) (ctx : ContractCallContext) st msg :=
    match msg with
    | Some msg => crowdfunding_receive_inner c ctx msg st
    | None => Err 0%nat
    end.

  Definition CF_MODULE :
    CameLIGOMod _ _ _ storage SimpleActionBody_rocq nat :=
    {| (* a name for the definition with the extracted code *)
      lmd_module_name := "cameLIGO_crowdfunding" ;

      (* definitions of operations on pairs and ints *)
      lmd_prelude :=
        (CameLIGOPrelude
          ++ nl
          ++ nl
          ++ "let test_account : address = (""tz1KqTpEZ7Yob7QbPE4Hy4Wo8fHG8LhKxZSx"" : address)"
          ++ nl
          ++ "let init_storage : (timestamp * (tez * address)) =
          (Tezos.get_now (), (42tez,(""tz1KqTpEZ7Yob7QbPE4Hy4Wo8fHG8LhKxZSx"": address)))")%bs;

      (* initial storage *)
      lmd_init := init ;

      (* init requires some extra operations *)
      lmd_init_prelude := "";

      lmd_receive_prelude := "";

      (* the main functionality *)
      lmd_receive := crowdfunding_receive;

      (* code for the entry point *)
      lmd_entry_point :=
      ("type storage = ((time_rocq * (tez * address)) * ((address,tez) map * bool))" ++ nl
       ++ CameLIGOPretty.printMain "crowdfunding_receive"
                                    "msg_rocq"
                                    "storage")%bs
    |}.

  (** We run the extraction procedure inside the [TemplateMonad].
      It uses the certified erasure from [MetaRocq] and the certified deboxing procedure
      that removes application of boxes to constants and constructors. *)

End Crowdfunding.

Section CrowdfundingExtraction.
  Import Crowdfunding.
  Import SimpleBlockchainExt.AcornBlockchain.
  Import CrowdfundingDataExt.
  Import CrowdfundingContract.Receive.

  Definition TT_remap_crowdfunding : list (kername * string) :=

  [ (* types *)
    remap <%% address_rocq %%> "address"
  ; remap <%% SimpleActionBody_rocq %%> "operation"
  ; remap <%% Maps.addr_map_rocq %%> "(address,tez) map"

  (* simple addresses and the execution layer addresses are treated as the same *)
  ; remap <%% @to_simple_ctx_addr %%> "(fun (x : address) -> x)"

  (* operations *)
  ; remap <%% eqb_addr %%> "eq_addr"
  ; remap <%% Maps.add_map %%> "Map.add"
  ; remap <%% lookup_map' %%> "Map.find_opt"
  ].

  (** A translation table of constructors and some constants. The corresponding definitions will be extracted and renamed. *)
  Definition TT_rename :=
    [ ("nil", "[]");
      ("mnil", "Map.empty") ].

  Time MetaRocq Run
       (CameLIGO_prepare_extraction [] TT_remap_crowdfunding (TT_rename ++ TT_rename_ctors_default) [] "cctx_instance" CF_MODULE).

  Time Definition cameLIGO_crowdfunding := Eval vm_compute in cameLIGO_crowdfunding_prepared.

  (** We redirect the extraction result for later processing and compiling with the CameLIGO compiler *)
  Redirect "cameligo-extract/CrowdfundingCertifiedExtraction.mligo"
  MetaRocq Run (tmMsg cameLIGO_crowdfunding).

End CrowdfundingExtraction.

(** * Extraction of various contracts to CameLIGO *)

From Coq Require Import ZArith.
From Coq Require Import List.
From Coq Require Import String.
From MetaCoq.Template Require Import All.
From ConCert.Embedding Require Import Notations.
From ConCert.Embedding.Extraction Require Import PreludeExt.
From ConCert.Embedding.Extraction Require SimpleBlockchainExt.
From ConCert.Examples.Crowdfunding Require Import CrowdfundingExt.
From ConCert.Examples.Crowdfunding Require CrowdfundingDataExt.
From ConCert.Extraction Require Import Common.
From ConCert.Extraction Require Import CameLIGOPretty.
From ConCert.Extraction Require Import CameLIGOExtract.
From ConCert.Execution Require Import Blockchain.

Import MonadNotation.

Local Open Scope string_scope.
Open Scope Z.

Existing Instance PrintConfShortNames.PrintWithShortNames.

Module Crowdfunding.

  Local Program Instance CB : ChainBase :=
  build_chain_base nat Nat.eqb _ _ _ _ Nat.odd. (* Odd addresses are addresses of contracts :) *)
Next Obligation.
  eapply NPeano.Nat.eqb_spec.
Defined.

  Notation storage := ((time_coq × Z × address_coq) × Maps.addr_map_coq × bool).

  Definition crowdfunding_init (ctx : ContractCallContext)
              (setup : (time_coq × Z × address_coq)) : option storage :=
      if ctx.(ctx_amount) =? 0 then Some (setup, (Maps.mnil, false)) else None.

  Definition init (setup : (time_coq × Z × address_coq)) : option storage :=
    Some (setup, (Maps.mnil, false)).

  Lemma crowdfunding_init_eq_init ctx setup :
    ctx.(ctx_amount) =? 0 -> (* no money should be sent on deployment *)
    crowdfunding_init ctx setup = init setup.
  Proof.
    intros Hamount. unfold crowdfunding_init. now rewrite Hamount.
  Qed.

  Open Scope Z.
  Import SimpleBlockchainExt.AcornBlockchain.
  Import CrowdfundingDataExt.
  Import CrowdfundingContract.Receive.

  Definition to_simple_ctx_addr (addr : Blockchain.Address) : address_coq :=
    if address_is_contract addr then ContractAddr_coq addr else
      UserAddr_coq addr.

  Definition crowdfunding_receive_inner
            (c : Chain)
            (ctx : ContractCallContext)
            (params : msg_coq)
            (st : storage) : option (list SimpleActionBody_coq × storage) :=
    receive params st
            (Time_coq c.(current_slot),
             (to_simple_ctx_addr ctx.(ctx_from),
             (ctx.(ctx_amount),
             ctx.(ctx_contract_balance)))).

  Definition crowdfunding_receive (c : Chain) (ctx : ContractCallContext) st msg :=
    match msg with
    | Some msg => crowdfunding_receive_inner c ctx msg st
    | None => None
    end.


  Definition CF_MODULE :
    CameLIGOMod _ _ _ storage SimpleActionBody_coq :=
    {| (* a name for the definition with the extracted code *)
      lmd_module_name := "cameLIGO_crowdfunding" ;

      (* definitions of operations on pairs and ints *)
      lmd_prelude :=
        CameLIGOPrelude
          ++ nl
          ++ nl
          ++ "let test_account : address = (""tz1KqTpEZ7Yob7QbPE4Hy4Wo8fHG8LhKxZSx"" : address)"
          ++ nl
          ++ "let init_storage :  (timestamp * (tez * address)) =
          (Tezos.now, (42tez,(""tz1KqTpEZ7Yob7QbPE4Hy4Wo8fHG8LhKxZSx"": address)))";

      (* initial storage *)
      lmd_init := init ;

      (* init requires some extra operations *)
      lmd_init_prelude := "";

      lmd_receive_prelude := "";

      (* the main functionality *)
      lmd_receive := crowdfunding_receive;

      (* code for the entry point *)
      lmd_entry_point :=
      "type storage = ((time_coq * (tez * address)) * ((address,tez) map * bool))" ++ nl
       ++ CameLIGOPretty.printMain "crowdfunding_receive"
                                    "msg_coq"
                                    "storage" |}.

  (** We run the extraction procedure inside the [TemplateMonad].
      It uses the certified erasure from [MetaCoq] and the certified deboxing procedure
      that removes application of boxes to constants and constructors. *)

End Crowdfunding.

Section CrowdfundingExtraction.
  Import Crowdfunding.
  Import SimpleBlockchainExt.AcornBlockchain.
  Import CrowdfundingDataExt.
  Import CrowdfundingContract.Receive.

  Definition TT_remap_crowdfunding : list (kername * string) :=

  [  (* types *)
    remap <%% address_coq %%> "address"
  ; remap <%% SimpleActionBody_coq %%> "operation"
  ; remap <%% Maps.addr_map_coq %%> "(address,tez) map"

  (* simple addresses and the execution layer addresses are treated as the same *)
  ; remap <%% to_simple_ctx_addr %%> "(fun (x : address) -> x)"

  (* operations *)
  ; remap <%% eqb_addr %%> "eq_addr"
  ; remap <%% Maps.add_map %%> "Map.add"
  ; remap <%% lookup_map' %%> "Map.find_opt"
  ].

  (** A translation table of constructors and some constants. The corresponding definitions will be extracted and renamed. *)
  Definition TT_rename :=
    [ ("nil", "[]");
      ("mnil", "Map.empty") ].

  Time MetaCoq Run
       (CameLIGO_prepare_extraction [] TT_remap_crowdfunding (TT_rename ++ TT_rename_ctors_default) [] "cctx_instance" CF_MODULE).

  Time Definition cameLIGO_crowdfunding := Eval vm_compute in cameLIGO_crowdfunding_prepared.

  MetaCoq Run (tmMsg cameLIGO_crowdfunding).

  (** We redirect the extraction result for later processing and compiling with the CameLIGO compiler *)
  Redirect "../extraction/tests/extracted-code/cameligo-extract/CrowdfundingCertifiedExtraction.mligo"
  MetaCoq Run (tmMsg cameLIGO_crowdfunding).

End CrowdfundingExtraction.

(** * Extraction of various contracts to CameLIGO *)

From Coq Require Import PeanoNat ZArith Notations.
From Coq Require Import List Ascii String Bool.

From MetaCoq.Template Require Import All.

From ConCert.Embedding Require Import Notations.
From ConCert.Embedding.Extraction Require Import SimpleBlockchainExt.
From ConCert.Embedding.Extraction Require Import PreludeExt.
From ConCert.Embedding.Extraction Require Import CrowdfundingData.
From ConCert.Embedding.Extraction Require Import Crowdfunding.
From ConCert.Embedding Require Import MyEnv CustomTactics.
From ConCert.Embedding Require Import Notations.
From ConCert.Extraction Require Import Common Optimize.
From ConCert.Extraction Require Import CameLIGOPretty CameLIGOExtract.
From ConCert.Execution Require Import Automation.
From ConCert.Execution Require Import Serializable.
From ConCert.Execution Require Import Blockchain.
From ConCert.Execution.Examples Require EIP20Token.
From ConCert.Execution Require Import Containers.
From ConCert.Utils Require Import RecordUpdate.
From ConCert.Utils Require Import StringExtra.

From stdpp Require gmap.


Local Open Scope string_scope.

Import MonadNotation.
Open Scope Z.

Existing Instance PrintConfShortNames.PrintWithShortNames.

Definition bindOptCont {A B} (a : option A) (f : A -> option B) : option B :=
  match a with
  | Some a => f a
  | None => None
  end.

Module SafeHead.
  (** This module shows how one can extract programs containing [False_rect] *)

  Open Scope list.
  Open Scope nat.

  (** We cannot make [safe_head] polymoprhic due to CameLIGO restrictions *)
  Program Definition safe_head (l : list nat) (non_empty : List.length l > 0) : nat :=
    match l as l' return l' = l -> nat  with
    | [] => (* this is an impossible case *)
      (* NOTE: we use [False_rect] to have more control over the extracted code. *)
      (* Leaving a hole for the whole branch potentially leads to polymoprhic *)
      (* definitions in the extracted code and type like [eq], since we would have to leave the whole goal branch transparent (use [Defined] instead of [Qed] ). *)
      (* In this case, one has to inspect the extracted code and inline such definitions *)
      fun _ => False_rect _ _
    | hd :: tl => fun _ => hd
    end eq_refl.
  Next Obligation.
    intros. subst. inversion non_empty.
  Qed.

  Import Lia.

  Program Definition head_of_list_2 (xs : list nat) := safe_head (0 :: 0 :: xs)  _.
  Next Obligation.
    intros. cbn. lia.
  Qed.

  (** We inline [False_rect] and [False_rec] to make sure that no polymoprhic definitions are left *)
  Definition safe_head_inline :=
    [<%% False_rect %%>; <%% False_rec %%>].

  Definition TT_consts := [ remap <%% @hd_error %%> "List.head_opt" ].
  Definition TT_ctors := [("O","0n")].

  Definition harness : string :=
    "let main (st : unit * nat option) : operation list * (nat option)  = (([]: operation list), Some (head_of_list_2 ([] : nat list)))".

    Time MetaCoq Run
         (t <- CameLIGO_extract_single
                safe_head_inline
                TT_consts
                (TT_ctors ++ TT_rename_ctors_default)
                ""
                harness
                head_of_list_2 ;;
    tmDefinition "cameligo_safe_head" t).

    (** Extraction results in fully functional CameLIGO code *)
    Redirect "examples/extracted-code/cameligo-extract/SafeHead.mligo"
    MetaCoq Run (tmMsg cameligo_safe_head).

End SafeHead.

Module Counter.

  (** Enabling recursors for records allows for deriving [Serializable] instances. *)
  Set Nonrecursive Elimination Schemes.

  (** The definitions in this section are generalized over the [ChainBase] that specifies the type of addresses and which properties such a type must have *)
  Notation address := nat.

  Definition operation := ActionBody.
  Definition storage := Z × address.

  Definition init (ctx : ContractCallContext) (setup : Z * address) : option storage :=
    let ctx_ := ctx in (* prevents optimisations from removing unused [ctx]  *)
    Some setup.

  Inductive msg :=
  | Inc (_ : Z)
  | Dec (_ : Z).

  Definition inc_balance (st : storage) (new_balance : Z) :=
    (st.1 + new_balance, st.2).

  Definition dec_balance (st : storage) (new_balance : Z) :=
    (st.1 - new_balance, st.2).

  Definition counter_inner (msg : msg) (st : storage)
    : option (list operation * storage) :=
    match msg with
    | Inc i =>
      if (0 <=? i) then
        Some ([],inc_balance st i)
      else None
    | Dec i =>
      if (0 <=? i) then
        Some ([],dec_balance st i)
      else None
    end.

  Definition counter (c : Chain) (ctx : ContractCallContext) st msg :=
    (* avoid erasing c and ctx arguments *)
    let c_ := c in
    let ctx_ := ctx in
    match msg with
    | Some msg =>counter_inner msg st
    | None => None
    end.

  Definition LIGO_COUNTER_MODULE : CameLIGOMod msg _ (Z × address) storage operation :=
    {| (* a name for the definition with the extracted code *)
        lmd_module_name := "cameLIGO_counter" ;

        (* and a test address *)
        lmd_prelude := CameLIGOPrelude ++ nl
                       ++ "let test_account : address = (""tz1KqTpEZ7Yob7QbPE4Hy4Wo8fHG8LhKxZSx"" : address)";

        (* initial storage *)
        lmd_init := init ;

        (* no extra operations in [init] are required *)
        lmd_init_prelude := "" ;

        (* the main functionality *)
        lmd_receive_prelude := "";

        lmd_receive := counter;

        (* code for the entry point *)
        lmd_entry_point :=
          CameLIGOPretty.printWrapper ("counter") "msg" "storage" ++ nl
          ++ CameLIGOPretty.printMain "storage" |}.

End Counter.
Section CounterExtraction.
  Import Lia.
  Import Counter.
  (** A translation table for definitions we want to remap. The corresponding top-level definitions will be *ignored* *)
  Definition TT_remap_counter : list (kername * string) :=
    [ remap <%% address_coq %%> "address"
    ; remap <%% time_coq %%> "timestamp"
    ; remap <%% nat %%> "address"
    ; remap <%% operation %%> "operation"
    ].

  (** We run the extraction procedure inside the [TemplateMonad]. *)
  (*       It uses the certified erasure from [MetaCoq] and the certified deboxing procedure *)
  (*       that removes application of boxes to constants and constructors. *)

  (** NOTE: running computations inside [TemplateMonad] is quite slow. That's why we comment out this code and use a different way below *)

  (* Time MetaCoq Run *)
  (*     (t <- CameLIGO_extract [] TT_remap_counter [] [] CameLIGO_call_ctx LIGO_COUNTER_MODULE ;; *)
  (*       tmDefinition LIGO_COUNTER_MODULE.(lmd_module_name) t). *)


  (*  If we first prepare the environment for erasure in [TemplateMonad] *)
  (*      and run erasure/prining outside of it, it works ~4 times faster for this example *)

  (** This command adds [cameLIGO_counter_prepared] to the environment, *)
  (*       which can be evaluated later *)
  Time MetaCoq Run
       (CameLIGO_prepare_extraction [] TT_remap_counter TT_rename_ctors_default [] "cctx_instance" LIGO_COUNTER_MODULE).

  Time Definition cameLIGO_counter_1 := Eval vm_compute in cameLIGO_counter_prepared.

  (** We redirect the extraction result for later processing and compiling with the CameLIGO compiler *)
  Redirect "examples/extracted-code/cameligo-extract/CounterCertifiedExtraction.mligo"
  MetaCoq Run (tmMsg cameLIGO_counter_1).

End CounterExtraction.

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

  Open Scope Z.
  Import ListNotations.
  Import AcornBlockchain.
  Import MonadNotation.
  Import CrowdfundingContract.
  Import Validate.
  Import Receive.

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
    CameLIGOMod _ _ (time_coq × Z × address_coq) storage SimpleActionBody_coq :=
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
      lmd_init := crowdfunding_init ;

      (* init requires some extra operations *)
      lmd_init_prelude := "";

      lmd_receive_prelude := "";

      (* the main functionality *)
      lmd_receive := crowdfunding_receive;

      (* code for the entry point *)
      lmd_entry_point :=
        "type storage = ((time_coq * (tez * address)) * ((address,tez) map * bool))" ++ CameLIGOPretty.printWrapper ("crowdfunding_receive")
                                    "msg_coq"
                                    "storage"
                                    ++ nl
                                    ++ CameLIGOPretty.printMain "storage" |}.

  (** We run the extraction procedure inside the [TemplateMonad].
      It uses the certified erasure from [MetaCoq] and the certified deboxing procedure
      that removes application of boxes to constants and constructors. *)

End Crowdfunding.

Section CrowdfundingExtraction.

  Import Crowdfunding.
  Import CrowdfundingContract.
  Import Validate.
  Import Receive.
  Import SimpleBlockchainExt.
  Import AcornBlockchain.

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
  Redirect "examples/extracted-code/cameligo-extract/CrowdfundingCertifiedExtraction.mligo"
  MetaCoq Run (tmMsg cameLIGO_crowdfunding).

End CrowdfundingExtraction.

Section EIP20TokenExtraction.

  Import EIP20Token.
  Import RecordSetNotations.

  Open Scope Z_scope.

  Definition init (ctx : ContractCallContext) (setup : EIP20Token.Setup) : option EIP20Token.State :=
    let ctx_ := ctx in
    Some {| total_supply := setup.(init_amount);
            balances := Common.AddressMap.add (EIP20Token.owner setup) (init_amount setup) Common.AddressMap.empty;
            allowances := Common.AddressMap.empty |}.

  Definition receive_ (chain : Chain)
       (ctx : ContractCallContext)
       (state : EIP20Token.State)
       (maybe_msg : option EIP20Token.Msg)
    : option (list ActionBody * EIP20Token.State) :=
    match EIP20Token.receive chain ctx state maybe_msg with
    | Some x => Some (x.2, x.1)
    | None => None
    end.
  Close Scope Z_scope.

  Definition LIGO_EIP20Token_MODULE : CameLIGOMod EIP20Token.Msg ContractCallContext EIP20Token.Setup EIP20Token.State ActionBody :=
  {| (* a name for the definition with the extracted code *)
      lmd_module_name := "cameLIGO_eip20token" ;

      (* definitions of operations on pairs and ints *)
      lmd_prelude := CameLIGOPrelude;

      (* initial storage *)
      lmd_init := init ;

      (* NOTE: printed as local [let]-bound definitions in the init *)
      lmd_init_prelude := "";

      (* TODO: maybe not needed, [lmd_prelude] should be enough *)
      lmd_receive_prelude := "";

      (* the main functionality *)
      lmd_receive := receive_ ;

      (* code for the entry point *)
      lmd_entry_point :=
        CameLIGOPretty.printWrapper "receive_" "msg" "state" ++ nl
        ++ CameLIGOPretty.printMain "state"|}.

  Definition TT_remap_eip20token : list (kername * string) :=
    TT_remap_default ++ [
    remap <%% @ContractCallContext %%> CameLIGO_call_ctx_type_name
  ; remap <%% @ctx_from %%> "ctx_from"
  ; remap <%% @ActionBody %%> "operation"

  ; remap <%% @FMap %%> "map"
  ; remap <%% @Common.AddressMap.add %%> "Map.add"
  ; remap <%% @Common.AddressMap.find %%> "Map.find_opt"
  ; remap <%% @Common.AddressMap.empty %%> "Map.empty"
  ].

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
  (CameLIGO_prepare_extraction TT_inlines_eip20token TT_remap_eip20token TT_rename_ctors_default [] "cctx_instance" LIGO_EIP20Token_MODULE).

  Time Definition cameLIGO_eip20token := Eval vm_compute in cameLIGO_eip20token_prepared.

  (** We redirect the extraction result for later processing and compiling with the CameLIGO compiler *)
  (* TODO: uncomment, once this fix https://gitlab.com/ligolang/ligo/-/merge_requests/1452 makes it
     into a release version. *)
  Redirect "examples/extracted-code/cameligo-extract/eip20tokenCertifiedExtraction.mligo"
  MetaCoq Run (tmMsg cameLIGO_eip20token).

End EIP20TokenExtraction.

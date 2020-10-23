(** * Extraction of various contracts to cameLIGO *)

From Coq Require Import PeanoNat ZArith Notations.

From MetaCoq.Template Require Import Loader.
From MetaCoq.Erasure Require Import Loader.

From ConCert.Embedding Require Import MyEnv CustomTactics.
From ConCert.Embedding Require Import Notations.
(* From ConCert.Embedding Require Import SimpleBlockchain. *)
From ConCert.Extraction Require Import Common Optimize PreludeExt.
From ConCert.Extraction Require Import CameLIGOPretty CameLIGOExtract.
From ConCert.Execution Require Import Automation.
From ConCert.Execution Require Import Serializable.
From ConCert.Execution Require Import Blockchain.

From ConCert.Extraction Require Import Common.
From ConCert.Extraction.Examples Require Import PreludeExt CrowdfundingData Crowdfunding.
From Coq Require Import List Ascii String.
Local Open Scope string_scope.

From MetaCoq.Template Require Import All.
Import MonadNotation.
Open Scope Z.

Definition PREFIX := "".

Module Counter.

  (** Enabling recursors for records allows for deriving [Serializable] instances. *)
  Set Nonrecursive Elimination Schemes.

  (** The definitions in this section are generalized over the [ChainBase] that specifies the type of addresses and which properties such a type must have *)
  Notation address := nat.

  Definition operation := ActionBody.
  Definition storage := Z × address.

  Definition init (ctx : SimpleCallCtx) (setup : Z * address) : option storage :=
    let ctx_ := ctx in (* prevents optimisations from removing unused [ctx]  *)
    Some setup.

  Inductive msg :=
  | Inc (_ : Z)
  | Dec (_ : Z).

  Definition inc_balance (st : storage) (new_balance : Z) :=
    (st.1 + new_balance, st.2).

  Definition dec_balance (st : storage) (new_balance : Z) :=
    (st.1 - new_balance, st.2).

  Definition counter (msg : msg) (st : storage)
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

  Definition LIGO_COUNTER_MODULE : CameLIGOMod msg _ (Z × address) storage operation :=
    {| (* a name for the definition with the extracted code *)
        lmd_module_name := "cameLIGO_counter" ;
    
        (* definitions of operations on pairs and ints *)
        lmd_prelude := CameLIGOPrelude;
    
        (* initial storage *)
        lmd_init := init ;
    
        (* no extra operations in [init] are required *)
        lmd_init_prelude := "" ;
    
        (* the main functionality *)
        lmd_receive := counter ;
    
        (* code for the entry point *)
        lmd_entry_point := CameLIGOPretty.printWrapper (PREFIX ++ "counter") "msg" "storage" ++ nl
                          ++ CameLIGOPretty.printMain |}.

  (** These definitions define a contract in a format required by the execution framework. Note that these definitions will not be used for extraction. We extract the definitions above instead. *)
  Definition counter_init (ch : Chain) (ctx : ContractCallContext) :=
    init_wrapper init ch ctx.

          Definition counter_receive (chain : Chain) (ctx : ContractCallContext)
                     (st : storage) (msg : option msg) : option (storage * list ActionBody)
            := match msg with
               | Some m => match counter m st with
                          | Some res => Some (res.2,res.1)
                          | None => None
                          end
               | None => None
               end.

          (** Deriving the [Serializable] instances for the state and for the messages *)
          Global Instance Msg_serializable : Serializable msg :=
            Derive Serializable msg_rect<Inc, Dec>.

  (** A contract instance used by the execution framework *)
  Program Definition CounterContract :=
    build_contract counter_init _ counter_receive _.
  Next Obligation. easy. Qed.

End Counter.
Section CounterExtraction.
  Import Lia.
  Import Counter.
  (* Require Coq.Numbers.BinNums. *)
  (* Print positive. *)
  (* Search positive. *)
  (** A translation table for definitions we want to remap. The corresponding top-level definitions will be *ignored* *)
  Definition TT_remap_counter : list (kername * string) :=
    [ remap <% bool %> "bool"
    ; remap <% list %> "list"
    ; remap <% Amount %> "tez"
    ; remap <% address_coq %> "address"
    ; remap <% time_coq %> "timestamp"
    ; remap <% option %> "option"
    ; remap <% Z.add %> "addInt"
    ; remap <% Z.sub %> "subInt"
    ; remap <% Z.leb %> "leInt"
    ; remap <% Z.eqb %> "eqInt"
    ; remap <% List.fold_left %> "List.fold"
    ; remap <% Z %> "int"
    ; remap <% nat %> "address"
    ; remap <% operation %> "operation"
    ; remap <% @fst %> "fst"
    ; remap <% positive %> "nat"
    ; remap <% Pos.add %> "addNat"
    ; remap <% Pos.sub %> "subNat"
    ; remap <% Pos.leb %> "leNat"
    ; remap <% @snd %> "snd"
    ; remap <% Pos.eqb %> "eqNat"
    (* TODO: set operations  *)
    ; remap <% Set %> "set" 
    ].

  (** A translation table of constructors and some constants. The corresponding definitions will be extracted and renamed. *)
  Definition TT_rename :=
    [ ("Some", "Some")
    ; ("None", "None")
    ; ("Z0" ,"0")
    ; ("xH" ,"1n")
    ; ("nil", "[]") ].

  (** We run the extraction procedure inside the [TemplateMonad].
      It uses the certified erasure from [MetaCoq] and the certified deboxing procedure
      that removes application of boxes to constants and constructors. *)

  (* Time MetaCoq Run
      (t <- CameLIGO_extraction PREFIX TT_remap_counter TT_rename LIGO_COUNTER_MODULE ;;
        tmDefinition LIGO_COUNTER_MODULE.(lmd_module_name) t).

  Print cameLIGO_counter.
  Redirect "./extraction/examples/cameligo-extract/CounterCertifiedExtraction.ligo" Compute cameLIGO_counter. *)
  
End CounterExtraction.

From ConCert.Extraction.Examples Require Import PreludeExt CrowdfundingData Crowdfunding SimpleBlockchainExt.
Module Crowdfunding.
  (* Import PreludeExt CrowdfundingData Crowdfunding SimpleBlockchainExt. *)
  Notation storage := ((time_coq × Z × address_coq) × Maps.addr_map_coq × bool).
  Notation params := ((time_coq × address_coq × Z × Z) × msg_coq).
  Definition crowdfunding_init (ctx : SimpleCallCtx)
            (setup : (time_coq × Z × address_coq)) : option storage :=
    if ctx.2.2.1 =? 0 then Some (setup, (Maps.mnil, false)) else None.
    (* (unfolded Init.init) setup ctx. *)
    Open Scope Z.
    Import ListNotations.
    Import AcornBlockchain.
    Import MonadNotation.
    Import CrowdfundingContract.
    Import Validate.
    Import Receive.
    
  Definition crowdfunding_receive
            (params : params)
            (st : storage) : option (list SimpleActionBody_coq × storage) :=
    receive params.2 st params.1.

  Definition double_quote := String (ascii_of_byte "034") "a".
  Open Scope string_scope.
  Definition CF_MODULE :
    CameLIGOMod params SimpleCallCtx (time_coq × Z × address_coq) storage SimpleActionBody_coq :=
    {| (* a name for the definition with the extracted code *)
      lmd_module_name := "cameLIGO_crowdfunding" ;

      (* definitions of operations on pairs and ints *)
      lmd_prelude :=
        CameLIGOPrelude
          ++ nl
          ++ "type storage = ((timestamp * (tez * address)) * ((address,tez) map * bool))"
          ++ nl
          ++ "let init_storage :  (timestamp * (tez * address)) =
          (Tezos.now, (42tez,(""tz1KqTpEZ7Yob7QbPE4Hy4Wo8fHG8LhKxZSx"": address)))";


      (* initial storage *)
      lmd_init := crowdfunding_init ;

      (* init requires some extra operations *)
      lmd_init_prelude := "";

      (* the main functionality *)
      lmd_receive := crowdfunding_receive  ;

      (* code for the entry point *)
      lmd_entry_point := CameLIGOPretty.printWrapper (PREFIX ++ "crowdfunding_receive") "((timestamp * (address * (tez * tez))) * msg_coq)" "storage" ++ nl
                        ++ CameLIGOPretty.printMain |}.


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
    remap <% Z %> "tez"
  ; remap <% address_coq %> "address"
  ; remap <% time_coq %> "timestamp"
  ; remap <% nat %> "nat"
  ; remap <% bool %> "bool"
  ; remap <% unit %> "unit"
  ; remap <% list %> "list"
  ; remap <% @fst %> "fst"
  ; remap <% @snd %> "snd"
  ; remap <% option %> "option"
  ; remap <% SimpleActionBody_coq %> "operation"
  ; remap <% Maps.addr_map_coq %> "(address,tez) map"
    (* 'amount' is a reserved keyword in ligo *)
  ; remap <% Amount %> "tez"

  (* operations *)
  ; remap <% Z.add %> "addTez"
  ; remap <% Z.sub %> "subTez"
  ; remap <% Z.leb %> "leTez"
  ; remap <% Z.ltb %> "ltTez"
  ; remap <% Z.eqb %> "eqTez"
  ; remap <% ltb_time %> "ltb_time"
  ; remap <% leb_time %> "leb_time"
  ; remap <% eqb_addr %> "eq_addr"
  ; remap <% andb %> "andb"
  ; remap <% negb %> "not"
  ; remap <% Maps.add_map %> "Map.add"
  ; remap <% lookup_map' %> "Map.find_opt" 
  ].

  Definition TT_rename_crowdfunding :=
    [ ("Z0" ,"0tez")
    ; ("nil", "[]")
    ; ("mnil", "Map.empty")
    ; ("tt", "()") ].

  (* Definition aa := "hello""aaaa".
  
  Redirect "./extraction/examples/cameligo-extract/CrowdfundingCertifiedExtraction.ligo" MetaCoq Run (tmMsg aa). *)
  

  Time MetaCoq Run
  (t <- CameLIGO_extraction PREFIX TT_remap_crowdfunding TT_rename_crowdfunding CF_MODULE ;;
    tmDefinition CF_MODULE.(lmd_module_name) t
  ).

  Print cameLIGO_crowdfunding.

  Open Scope string.
  Definition printed := Eval vm_compute in cameLIGO_crowdfunding.
    (** We redirect the extraction result for later processing and compiling with the CameLIGO compiler *)
  Redirect "./extraction/examples/cameligo-extract/CrowdfundingCertifiedExtraction.ligo" MetaCoq Run (tmMsg printed).

End CrowdfundingExtraction.

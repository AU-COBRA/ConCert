(** * Extraction of various contracts to cameLIGO *)

From Coq Require Import PeanoNat ZArith Notations.

From MetaCoq.Template Require Import Loader.
From MetaCoq.Erasure Require Import Loader.

From ConCert.Embedding Require Import MyEnv CustomTactics.
From ConCert.Embedding Require Import Notations.
From ConCert.Embedding Require Import SimpleBlockchain.
From ConCert.Extraction Require Import Common Optimize PreludeExt.
From ConCert.Extraction Require Import CameLIGOPretty CameLIGOExtract.
From ConCert.Execution Require Import Automation.
From ConCert.Execution Require Import Serializable.
From ConCert.Execution Require Import Blockchain.
From Coq Require Import List Ascii String.
Local Open Scope string_scope.

From MetaCoq.Template Require Import All.

Import ListNotations.
Import AcornBlockchain.
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

Import Lia.
Import Counter.

(** A translation table for definitions we want to remap. The corresponding top-level definitions will be *ignored* *)
Definition TT_remap : list (kername * string) :=
  [ remap <% bool %> "bool"
  ; remap <% list %> "list"
  ; remap <% Amount %> "tez"
  ; remap <% address_coq %> "address"
  ; remap <% time_coq %> "timestamp"
  ; remap <% option %> "option"
  ; remap <% Z.add %> "addInt"
  ; remap <% Z.sub %> "subInt"
  ; remap <% Z.leb %> "leInt"
  ; remap <% List.fold_left %> "List.fold"
  ; remap <% Z %> "int"
  ; remap <% nat %> "address"
  ; remap <% operation %> "operation"
  ; remap <% @fst %> "fst"
  ; remap <% @snd %> "snd"
   (* TODO: set operations  *)
  ; remap <% Set %> "set" 
  ].

(** A translation table of constructors and some constants. The corresponding definitions will be extracted and renamed. *)
Definition TT_rename :=
  [ ("Some", "Some")
  ; ("None", "None")
  ; ("Z0" ,"0")
  ; ("nil", "[]") ].

(** We run the extraction procedure inside the [TemplateMonad].
    It uses the certified erasure from [MetaCoq] and the certified deboxing procedure
    that removes application of boxes to constants and constructors. *)

Time MetaCoq Run
     (t <- CameLIGO_extraction PREFIX TT_remap TT_rename LIGO_COUNTER_MODULE ;;
      tmDefinition LIGO_COUNTER_MODULE.(lmd_module_name) t).

Print cameLIGO_counter.
Redirect "./extraction/examples/cameligo-extract/CounterCertifiedExtraction.ligo" Compute cameLIGO_counter.

Module Crowdfunding.

  Notation storage := ((time_coq × Z × address_coq) × Maps.addr_map_coq × bool).
  Notation params := ((time_coq × address_coq × Z × Z) × msg_coq).
  Definition crowdfunding_init (ctx : SimpleCallCtx)
            (setup : (time_coq × Z × address_coq)) : option storage :=
    if ctx.2.2.1 =? 0 then Some (setup, (Maps.mnil, false)) else None.
    (* (unfolded Init.init) setup ctx. *)

  Definition crowdfunding_receive
            (params : params)
            (st : storage) : option (list SimpleActionBody_coq × storage) :=
    receive params.2 st params.1.

  Definition COUNTER_MODULE :
    CameLIGOMod params SimpleCallCtx (time_coq × Z × address_coq) storage SimpleActionBody_coq :=
    {| (* a name for the definition with the extracted code *)
      lmd_module_name := "cameligo_crowdfunding" ;

      (* definitions of operations on pairs and ints *)
      lmd_prelude :=
        CameLIGOPrelude
          ++ nl
          ++ "type storage = ((timestamp * (tez * address)) * ((address,tez) map * bool))";

      (* initial storage *)
      lmd_init := crowdfunding_init ;

      (* init requires some extra operations *)
      lmd_init_prelude :=
              "let fst (p : 'a * 'b) : 'a = p.(0) in"
          ++ nl
          ++ "let snd (p : 'a * 'b) : 'b = p.(1) in"
          ++ nl
          ++ "let eqTez (a : tez ) (b : tez ) = a = b in" ;


      (* the main functionality *)
      lmd_receive := crowdfunding_receive  ;

      (* code for the entry point *)
      lmd_entry_point := printWrapperAndMain |}.

  (** We run the extraction procedure inside the [TemplateMonad].
      It uses the certified erasure from [MetaCoq] and the certified deboxing procedure
      that removes application of boxes to constants and constructors. *)

End Crowdfunding.

Import Crowdfunding.

Time MetaCoq Run
(t <- CameLIGO_extraction PREFIX TT_remap TT_rename COUNTER_MODULE ;;
  tmDefinition COUNTER_MODULE.(lmd_module_name) t
).

Print CameLIGO_crowdfunding.

(** We redirect the extraction result for later processing and compiling with the CameLIGO compiler *)
Redirect "./extraction/examples/CameLIGO-extract/CrowdfundingCertifiedExtraction.liq" Compute CameLIGO_crowdfunding.

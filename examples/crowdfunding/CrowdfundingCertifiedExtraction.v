(** * Extraction of a crowdfunding contract *)

From Coq Require Import ZArith.
From Coq Require Import String.
From ConCert.Embedding Require Import Notations.
From ConCert.Extraction Require Import LiquidityExtract.
From ConCert.Extraction Require Import LPretty.
From ConCert.Extraction Require Import Common.
From ConCert.Extraction Require Import ResultMonad.
From ConCert.Embedding.Extraction Require Import PreludeExt.
From ConCert.Embedding.Extraction Require Import SimpleBlockchainExt.
From ConCert.Examples.Crowdfunding Require Import CrowdfundingDataExt.
From ConCert.Examples.Crowdfunding Require Import CrowdfundingExt.
From MetaCoq.Template Require Import All.

Import AcornBlockchain.
Import MCMonadNotation.
Import CrowdfundingContract.
Import Receive.

Local Open Scope string_scope.
Open Scope Z.

Definition PREFIX := "".

(** A translation table for definitions we want to remap. The corresponding top-level definitions will be *ignored* *)
Definition TT_remap : list (kername * String.string) :=
  [  (* types *)
    remap <%% Z %%> "tez"
  ; remap <%% address_coq %%> "address"
  ; remap <%% time_coq %%> "timestamp"
  ; remap <%% nat %%> "nat"
  ; remap <%% bool %%> "bool"
  ; remap <%% unit %%> "unit"
  ; remap <%% list %%> "list"
  ; remap <%% @fst %%> "fst"
  ; remap <%% @snd %%> "snd"
  ; remap <%% option %%> "option"
  ; remap <%% Maps.addr_map_coq %%> "(address,tez) map"
  ; remap <%% SimpleActionBody_coq %%> "operation"

  (* operations *)
  ; remap <%% Z.add %%> "addTez"
  ; remap <%% Z.eqb %%> "eqTez"
  ; remap <%% Z.leb %%> "leTez"
  ; remap <%% Z.ltb %%> "ltTez"
  ; remap <%% ltb_time %%> "ltb_time"
  ; remap <%% leb_time %%> "leb_time"
  ; remap <%% eqb_addr %%> "eq_addr"
  ; remap <%% andb %%> "andb"
  ; remap <%% negb %%> "not"
  ; remap <%% Maps.add_map %%> "Map.add"
  ; remap <%% lookup_map' %%> "Map.find" ].

(** A translation table of constructors and some constants. The corresponding definitions will be extracted and renamed. *)
Definition TT_rename :=
  [ ("Z0" ,"0DUN")
  ; ("nil", "[]")
  ; ("mnil", "Map []")
  ; ("tt", "()")
  ; ("true", "true")
  ; ("false", "false")].

Definition printWrapperAndMain :=
  "let wrapper (msg : msg_coq)(st : ((timestamp * (tez * address)) * ((address,tez) map * bool))) = match receive msg st (Current.time (), (Current.sender (), (Current.amount (), Current.balance ()))) with
| Ok v -> v| Err e -> failwith e" ++ Common.nl ++ Common.nl++
"let%entry main (msg : msg_coq)(st : ((timestamp * (tez * address)) * ((address,tez) map * bool))) = wrapper msg st".


Notation storage := ((time_coq × Z × address_coq) × Maps.addr_map_coq × bool).
Notation params := ((time_coq × address_coq × Z × Z) × msg_coq).
Definition crowdfunding_init (ctx : SimpleCallCtx)
                             (setup : (time_coq × Z × address_coq))
                             : ConCert.Execution.ResultMonad.result storage nat :=
  if ctx.2.2.1 =? 0
  then ConCert.Execution.ResultMonad.Ok (setup, (Maps.mnil, false))
  else ConCert.Execution.ResultMonad.Err 0%nat.
  (* (unfolded Init.init) setup ctx. *)

Definition crowdfunding_receive
           (params : params)
           (st : storage)
           : ConCert.Execution.ResultMonad.result (list SimpleActionBody_coq × storage) nat :=
  match receive params.2 st params.1 with
  | Some v => ConCert.Execution.ResultMonad.Ok v
  | None => ConCert.Execution.ResultMonad.Err 0%nat
  end.

Definition CROWDFUNDING_MODULE :
  LiquidityMod params SimpleCallCtx (time_coq × Z × address_coq) storage SimpleActionBody_coq nat :=
  {| (* a name for the definition with the extracted code *)
     lmd_module_name := "liquidity_crowdfunding" ;

     (* definitions of operations on pairs and ints *)
     lmd_prelude :=
       LiquidityPrelude
         ++ Common.nl
         ++ "type storage = ((timestamp * (tez * address)) * ((address,tez) map * bool))";

     (* initial storage *)
     lmd_init := crowdfunding_init ;

     (* init requires some extra operations *)
     lmd_init_prelude :=
            "let fst (p : 'a * 'b) : 'a = p.(0) in"
         ++ Common.nl
         ++ "let snd (p : 'a * 'b) : 'b = p.(1) in"
         ++ Common.nl
         ++ "let eqTez (a : tez ) (b : tez ) = a = b in" ;


     (* the main functionality *)
     lmd_receive := crowdfunding_receive  ;

     (* code for the entry point *)
     lmd_entry_point := printWrapperAndMain |}.

(** We run the extraction procedure inside the [TemplateMonad].
    It uses the certified erasure from [MetaCoq] and the certified deboxing procedure
    that removes application of boxes to constants and constructors. *)

Time MetaCoq Run
     (t <- liquidity_extraction PREFIX TT_remap TT_rename [] CROWDFUNDING_MODULE ;;
      tmDefinition (String.of_string CROWDFUNDING_MODULE.(lmd_module_name)) t
     ).

Print liquidity_crowdfunding.

(** We redirect the extraction result for later processing and compiling with the Liquidity compiler *)
Redirect "../extraction/tests/extracted-code/liquidity-extract/CrowdfundingCertifiedExtraction.liq" Compute liquidity_crowdfunding.

Require Import String ZArith Basics.
From ConCert.Embedding Require Import Ast Notations CustomTactics
     PCUICTranslate PCUICtoTemplate Utils MyEnv.

From ConCert.Extraction Require Import LiquidityExtract LPretty Common.
From ConCert.Extraction.Examples Require Import PreludeExt CrowdfundingData Crowdfunding SimpleBlockchainExt.

From Coq Require Import List Ascii String.
Local Open Scope string_scope.

From MetaCoq.Template Require Import All.

Import ListNotations.
Import AcornBlockchain.
Import MonadNotation.

Open Scope Z.

Import CrowdfundingContract.
Import Validate.
Import Receive.

Definition PREFIX := "".

(** A translation table for definitions we want to remap. The corresponding top-level definitions will be *ignored* *)
Definition TT_remap : list (kername * string) :=
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
  ; remap <% Maps.addr_map_coq %> "(address,tez) map"
  ; remap <% SimpleActionBody_coq %> "operation"

  (* operations *)
  ; remap <% Z.add %> "addTez"
  ; remap <% Z.eqb %> "eqTez"
  ; remap <% Z.leb %> "leTez"
  ; remap <% Z.ltb %> "ltTez"
  ; remap <% ltb_time %> "ltb_time"
  ; remap <% leb_time %> "leb_time"
  ; remap <% eqb_addr %> "eq_addr"
  ; remap <% andb %> "andb"
  ; remap <% negb %> "not"
  ; remap <% Maps.add_map %> "Map.add"
  ; remap <% lookup_map' %> "Map.find" ].

(** A translation table of constructors and some constants. The corresponding definitions will be extracted and renamed. *)
Definition TT_rename :=
  [ ("Z0" ,"0DUN")
  ; ("nil", "[]")
  ; ("mnil", "Map []")
  ; ("tt", "()") ].

Definition printWrapperAndMain :=
  "let wrapper (msg : msg_coq)(st : ((timestamp * (tez * address)) * ((address,tez) map * bool))) = match receive msg st (Current.time (), (Current.sender (), (Current.amount (), Current.balance ()))) with
| Some v -> v| None -> failwith ()" ++ nl ++ nl++
"let%entry main (msg : msg_coq)(st : ((timestamp * (tez * address)) * ((address,tez) map * bool))) = wrapper msg st".


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
  LiquidityMod params SimpleCallCtx (time_coq × Z × address_coq) storage SimpleActionBody_coq :=
  {| (* a name for the definition with the extracted code *)
     lmd_module_name := "liquidity_crowdfunding" ;

     (* definitions of operations on pairs and ints *)
     lmd_prelude :=
       LiquidityPrelude
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

Time MetaCoq Run
     (t <- liquitidy_extraction PREFIX TT_remap TT_rename COUNTER_MODULE ;;
      tmDefinition COUNTER_MODULE.(lmd_module_name) t
     ).

Print liquidity_crowdfunding.

(** We redirect the extraction result for later processing and compiling with the Liquidity compiler *)
Redirect "./extraction/examples/liquidity-extract/CrowdfundingCertifiedExtraction.liq" Compute liquidity_crowdfunding.

Require Import String ZArith Basics.
From ConCert.Embedding Require Import Ast Notations CustomTactics
     PCUICTranslate PCUICtoTemplate Utils MyEnv.

From ConCert.Extraction Require Import Certified LPretty.
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

Definition local_def := local PREFIX.

(** A translation table for various constants we want to rename *)
Definition TT : env string :=
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
     ; remap <% lookup_map' %> "Map.find"

     ; ("Z0" ,"0DUN")
     ; ("nil", "[]")
     ; ("tt", "()")

     ; local_def <% msg_coq %>

     ; local_def <% update_contribs %>
     ; local_def <% maybe_bind_unit %>
     ; local_def <% set_done %>
     ; local_def <% validate %>
  ].


Definition printWrapperAndMain :=
  "let wrapper (msg : msg_coq)(st : ((timestamp * (tez * address)) * ((address,tez) map * bool))) = match receive msg st (Current.time (), (Current.sender (), (Current.amount (), Current.balance ()))) with
| Some v -> v| None -> failwith ()
let%entry main (msg : msg_coq)(st : ((timestamp * (tez * address)) * ((address,tez) map * bool))) = wrapper msg st".

Time MetaCoq Run
     (ind <- tmQuoteInductive <%% msg_coq %%> ;;
     ind_liq <- print_one_ind_body PREFIX TT ind.(ind_bodies);;
     t1 <- toLiquidity PREFIX TT update_contribs ;;
     t2 <- toLiquidity PREFIX TT maybe_bind_unit ;;
     t3 <- toLiquidity PREFIX TT set_done ;;
     t4 <- toLiquidity PREFIX TT validate ;;
     t5 <- toLiquidity PREFIX TT receive ;;
     res <- tmEval lazy
                  (LiquidityPrelude
                     ++ nl ++ nl
                     ++ "type storage = ((timestamp * (tez * address)) * ((address,tez) map * bool))"
                     ++ nl ++ nl
                     ++ ind_liq
                     ++ nl ++ nl
                     ++ t1
                     ++ nl ++ nl
                     ++ t2
                     ++ nl ++ nl
                     ++ t3
                     ++ nl ++ nl
                     ++ t4
                     ++ nl ++ nl
                     ++ t5
                     ++ nl ++ nl
                     ++ printWrapperAndMain ) ;;
    tmDefinition "crowdfunding_extracted" res).

Print crowdfunding_extracted.

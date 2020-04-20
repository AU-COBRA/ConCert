Require Import String ZArith Basics.
From ConCert.Embedding Require Import Ast Notations CustomTactics
     PCUICTranslate PCUICtoTemplate Utils MyEnv.

From ConCert.Extraction Require Import Certified LPretty.
From ConCert.Extraction.Examples Require Import Prelude CrowdfundingData Crowdfunding SimpleBlockchain.

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
     ; remap <% option %> "option"
     ; remap <% addr_map %> "(address,tez) map"
     ; remap <% SimpleActionBody %> "operation"

     ; remap <% Z.add %> "addTez"
     ; remap <% Z.eqb %> "eqTez"
     ; remap <% Z.leb %> "leTez"
     ; remap <% Z.ltb %> "ltTez"
     ; remap <% ltb_time %> "ltb_time"
     ; remap <% leb_time %> "leb_time"
     ; remap <% eqb_addr %> "eq_addr"
     ; remap <% andb %> "andb"
     ; remap <% negb %> "not"
     ; remap <% add_map %> "Map.add"
     ; remap <% lookup %> "Map.find"

     ; ("Z0" ,"0DUN")
     ; ("nil", "[]")
     ; ("tt", "()")

     ; local <% msg_coq %>

     ; local <% @fst %>
     ; local <% @snd %>

     ; local <% update_contribs %>
     ; local <% maybe_bind_unit %>
     ; local <% set_done %>
     ; local <% validate %>

  ].


Definition printWrapperAndMain :=
  "let wrapper (msg : msg_coq)(st : ((timestamp * (tez * address)) * ((address,tez) map * bool))) = match receive msg st (Current.time (), (Current.sender (), (Current.amount (), Current.balance ()))) with
| Some v -> v| None -> failwith ()
let%entry main (msg : msg_coq)(st : ((timestamp * (tez * address)) * ((address,tez) map * bool))) = wrapper msg st".

Time Run TemplateProgram
     (
     (* storage_def <- tmQuoteConstant "storage" false ;; *)
     (* storage_body <- opt_to_template storage_def.(cst_body) ;; *)
     ind <- tmQuoteInductive "msg_coq" ;;
     ind_liq <- print_one_ind_body TT ind.(ind_bodies);;
     t1 <- toLiquidity TT update_contribs ;;
     t2 <- toLiquidity TT maybe_bind_unit ;;
     t3 <- toLiquidity TT set_done ;;
     t4 <- toLiquidity TT validate ;;
     t5 <- toLiquidity TT receive ;;
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

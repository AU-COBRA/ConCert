From Coq Require Import PeanoNat ZArith Notations.

From MetaCoq.Template Require Import Loader.

From ConCert Require Import MyEnv.
From ConCert.Embedding Require Import Notations.
From ConCert.Embedding Require Import SimpleBlockchain.
From ConCert.Extraction Require Import LPretty Certified.
From ConCert.Extraction Require Import Counter.

From Coq Require Import List Ascii String.
Local Open Scope string_scope.

From MetaCoq.Template Require Import All.

Import ListNotations.
Import AcornBlockchain.
Import MonadNotation.

Open Scope Z.

Module Counter.

  Definition storage := Z × nat.

  Inductive msg :=
  | Inc (_ : Z)
  | Dec (_ : Z).

  Definition inc_balance (st : storage) (new_balance : Z) :=
    (st.1 + new_balance, st.2).

  Definition dec_balance (st : storage) (new_balance : Z) :=
    (st.1 - new_balance, st.2).

  Definition counter (msg : msg) (st : storage)
    : option (list SimpleActionBody * storage) :=
    match msg with
    | Inc i =>
      if (0 <=? i) then
        Some ([], inc_balance st i)
      else None
    | Dec i =>
      if (0 <=? i) then
        Some ([], dec_balance st i)
      else None
    end.

End Counter.


Import Counter.

(** A translation table for various constants we want to rename *)
Definition TT : env string :=
  [  remap <% Z.add %> "addTez"
     ; remap <% Z.sub %> "subTez"
     ; remap <% Z.leb %> "lebTez"
     ; remap <% Z %> "tez"
     ; remap <% nat %> "address"
     ; ("Z0" ,"0DUN")
     ; ("nil", "[]")
     ; local <% @fst %>
     ; local <% @snd %>
     ; local <% inc_balance %>
     ; local <% dec_balance %>
  ].


(** We run the extraction procedure isude the [TemplateMonad]. It uses the certified erasure from [MetaCoq] and (so far uncertified) de-boxing procedure that remove redundant type abstractions and application of boxes *)
Run TemplateProgram
    (storage_def <- tmQuoteConstant "storage" false ;;
     storage_body <- opt_to_template storage_def.(cst_body) ;;
     ind <- tmQuoteInductive "msg" ;;
     ind_liq <- get_one_ind_body TT ind.(ind_bodies);;
     t1 <- toLiquidity TT inc_balance ;;
     t2 <- toLiquidity TT dec_balance ;;
     t3 <- toLiquidity TT counter ;;
     res <-
     tmEval lazy
            (LiquidityPrelude
               ++ nl ++ nl
               ++ "type storage = " ++ print_liq_type TT storage_body
               ++ nl ++ nl
               ++ ind_liq
               ++ nl ++ nl
               ++ t1
               ++ nl ++ nl
               ++ t2
               ++ nl ++ nl
               ++ t3
               ++ nl ++ nl
               ++ printWrapper "counter"
               ++ nl ++ nl
               ++ printMain) ;;
     tmPrint res).

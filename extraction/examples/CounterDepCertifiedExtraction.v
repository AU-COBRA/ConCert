From Coq Require Import PeanoNat ZArith Notations Bool.

From MetaCoq.Template Require Import Loader.
From MetaCoq.Erasure Require Import Loader.

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

Import Lia.

Module Counter.

  Definition storage := Z × nat.

  Inductive msg :=
  | Inc (_ : Z)
  | Dec (_ : Z).

  Definition inc_balance (st :  Z × nat) (new_balance : Z)
               (p : (0 <=? new_balance) = true) :=
    (st.1 + new_balance, st.2).


  Definition dec_balance (st : storage) (new_balance : Z)
             (p : (0 <=? new_balance) = true) :=
    (st.1 -  new_balance, st.2).

  Definition my_bool_dec := Eval compute in bool_dec.

  Definition counter (msg : msg) (st : storage)
    : option (list SimpleActionBody * storage) :=
    match msg with
    | Inc i =>
      match (my_bool_dec (0 <=? i) true) with
      | left h =>
        Some ([], inc_balance st i h)
      | right _ => None
      end
    | Dec i =>
      match (my_bool_dec (0 <=? i) true) with
      | left h => Some ([], dec_balance st i h)
      | right _ => None
      end
    end.

End Counter.

Import Counter.

(** A translation table for various constants we want to rename *)
Definition TT : env string :=
  [  remap <% Z.add %> "addInt"
     ; remap <% Z.sub %> "subInt"
     ; remap <% Z.leb %> "leInt"
     ; remap <% Z %> "int"
     ; remap <% bool %> "bool"
     ; remap <% nat %> "address"
     ; ("left", "Left")
     ; ("right", "Right")
     ; ("Z0" ,"0")
     ; ("nil", "[]")
     ; local <% @fst %>
     ; local <% @snd %>
     ; local <% storage %>
     ; local <% msg %>
     ; local <% inc_balance %>
     ; local <% dec_balance %>
     ; local <% my_bool_dec %>
  ].

Quote Recursively Definition ex_partially_applied_syn :=
  ((fun msg : msg => fun st => match msg with
    | Inc i =>
      match (my_bool_dec (0 <=? i) true) with
      | left h =>
        let f := inc_balance st i in
        Some ([], f h)
      | right _ => None
      end
    | Dec i =>
      match (my_bool_dec (0 <=? i) true) with
      | left h => Some ([], dec_balance st i h)
      | right _ => None
      end
    end) : msg -> storage -> option (list SimpleActionBody * storage)).

Compute (erase_and_check_applied ex_partially_applied_syn).
(* returns [false], as expected *)

(** We run the extraction procedure inside the [TemplateMonad]. It uses the certified erasure from [MetaCoq] and (so far uncertified) de-boxing procedure that removes application of boxes to constants and constructors. Even though the de-boxing is not certified yet, before removing boxes we check if constant is applied to all logical argument (i.e. proofs or types) and constructors are fully applied. In this case, it is safe to remove these applications. *)
Run TemplateProgram
    (storage_def <- tmQuoteConstant "storage" false ;;
     storage_body <- opt_to_template storage_def.(cst_body) ;;
     ind <- tmQuoteInductive "msg" ;;
     ind_liq <- print_one_ind_body TT ind.(ind_bodies);;
     t1 <- toLiquidity TT inc_balance ;;
     t2 <- toLiquidity TT dec_balance ;;
     t3 <- toLiquidity TT my_bool_dec ;;
     t4 <- toLiquidity TT counter ;;
     res <- tmEval lazy
                  (prod_ops ++ nl ++ int_ops
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
                     ++ t4
                     ++ nl ++ nl
                     ++ printWrapper "counter"
                     ++ nl ++ nl
                     ++ printMain) ;;
    tmDefinition "counter_extracted" res).

Print counter_extracted.

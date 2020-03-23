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

  Definition non_neg := {z : Z | 0 <= z}.

  Definition none {A} := None (A:=A).
  Definition some {A} := Some (A:=A).

  Inductive msg :=
  | Inc (_ : Z)
  | Dec (_ : Z).

  Definition inc_balance (st : storage) (new_balance : Z)
               (p : (0 <=? new_balance) = true) :=
    (st.1 + new_balance, st.2).


  Definition dec_balance (st : storage) (new_balance : non_neg) :=
    (st.1 -  proj1_sig new_balance, st.2).

  Definition geb_non_neg : forall i, (0 <=? i) = true -> non_neg.
    intros i H. apply Z.leb_le in H. exists i. exact H.
  Qed.

  Definition my_bool_dec := Eval compute in bool_dec.

  Definition counter (msg : msg) (st : storage)
    : option (list SimpleActionBody * storage) :=
    match msg with
    | Inc i =>
      match (my_bool_dec (0 <=? i) true) with
      | left H => some ([], inc_balance st i H)
      | right _ => none
      end
    | Dec i =>
      (* for simplicity, return [None] here *)
      none
      (* if bool_dec (0 <=? i) true then *)
      (*   Some ([], dec_balance st (geb_non_neg i _)) *)
      (* else None *)
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
     ; ("left", "Left")
     ; ("right", "Right")
     ; ("Z0" ,"0DUN")
     ; local <% @nil %>
     ; local <% @none %>
     ; local <% @some %>
     ; local <% @fst %>
     ; local <% @snd %>
     ; local <% inc_balance %>
     ; local <% my_bool_dec %>
  ].

Definition LiquidityPreludeAlt :=
       "let[@inline] fst (p : 'a * 'b) : 'a = p.(0)"
    ++ nl
    ++ "let[@inline] snd (p : 'a * 'b) : 'b = p.(1)"
    ++ nl

    ++ "let[@inline] none (u1 : unit) = None"
    ++ nl
    ++ "let[@inline] some (u1 : unit) = Some"
    ++ nl
    ++ "let[@inline] nil (u1 : unit) : operation list = []"
    ++ nl
    ++ "let[@inline] pair (u1 : unit) (u1 : unit) (a : 'a) (b : 'b) = (a,b)"

    ++ "let[@inline] addN (n : nat) (m : nat) = n + m"
    ++ nl
    ++ "let[@inline] addTez (n : tez) (m : tez) = n + m"
    ++ nl
    ++ "let[@inline] subTez (n : tez) (m : tez) = n - m"
    ++ nl
    ++ "let[@inline] andb (a : bool ) (b : bool ) = a & b"
    ++ nl
    ++ "let[@inline] lebN (a : nat ) (b : nat ) = a <= b"
    ++ nl
    ++ "let[@inline] ltbN (a : nat ) (b : nat ) = a < b"
    ++ nl
    ++ "let[@inline] lebTez (a : tez ) (b : tez ) = a<=b"
    ++ nl
    ++ "let[@inline] ltbTez (a : tez ) (b : tez ) = a<b"
    ++ nl
    ++ "let[@inline] eqN (a : nat ) (b : nat ) = a = b"
    ++ nl
    ++ "let[@inline] eqb_addr (a1 : address) (a2 : address) = a1 = a2"
    ++ nl
    ++ "let[@inline] eqb_time (a1 : timestamp) (a2 : timestamp) = a1 = a2"
    ++ nl
    ++ "let[@inline] leb_time (a1 : timestamp) (a2 : timestamp) = a1 <= a2"
    ++ nl
    ++ "let[@inline] ltb_time (a1 : timestamp) (a2 : timestamp) = a1 < a2".


(** We run the extraction procedure isude the [TemplateMonad]. It uses the certified erasure from [MetaCoq] and (so far uncertified) de-boxing procedure that remove redundant type abstractions and application of boxes *)
Run TemplateProgram
    (storage_def <- tmQuoteConstant "storage" false ;;
     storage_body <- opt_to_template storage_def.(cst_body) ;;
     ind <- tmQuoteInductive "msg" ;;
     ind_liq <- get_one_ind_body TT ind.(ind_bodies);;
     t1 <- toLiquidityWithBoxes TT inc_balance ;;
     t2 <- toLiquidityWithBoxes TT my_bool_dec ;;
     t3 <- toLiquidityWithBoxes TT counter ;;
     res <-
     tmEval lazy
            (LiquidityPreludeAlt
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

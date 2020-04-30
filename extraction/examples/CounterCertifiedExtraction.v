From Coq Require Import PeanoNat ZArith Notations.

From MetaCoq.Template Require Import Loader.

From ConCert.Embedding Require Import MyEnv CustomTactics.
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

  Notation address := nat.

  Definition storage := Z × address.

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

Import Lia.

Lemma inc_correct state n m :
  0 <= m ->
  state.1 = n ->
  exists new_state, counter (Inc m) state = Some ([],new_state)
                    /\ new_state.1 = (n + m)%Z.
Proof.
  intros Hm Hn.
  eexists. split.
  - simpl. destruct ?; Zleb_ltb_to_prop;auto;lia.
  - simpl. congruence.
Qed.

Lemma dec_correct state n m :
  0 <= m ->
  state.1 = n ->
  exists new_state, counter (Dec m) state = Some ([],new_state)
                    /\ new_state.1 = (n - m)%Z.
Proof.
  intros Hm Hn.
  eexists. split.
  - simpl. destruct ?; Zleb_ltb_to_prop;auto;lia.
  - simpl. congruence.
Qed.

Import Counter.

(** A translation table for various constants we want to rename *)
Definition TT : env string :=
  [  remap <% Z.add %> "addInt"
     ; remap <% Z.sub %> "subInt"
     ; remap <% Z.leb %> "leInt"
     ; remap <% Z %> "int"
     ; remap <% nat %> "address"
     ; ("Z0" ,"0")
     ; ("nil", "[]")
     ; local <% @fst %>
     ; local <% @snd %>
     ; local <% storage %>
     ; local <% msg %>
     ; local <% inc_balance %>
     ; local <% dec_balance %>
  ].

Quote Recursively Definition counter_syn := (unfolded counter).

Time Eval vm_compute in (erase_and_check_applied counter_syn).
Time Eval vm_compute in (erase_print_deboxed_all_applied TT counter_syn).

(** We run the extraction procedure inside the [TemplateMonad]. It uses the certified erasure from [MetaCoq] and (so far uncertified) de-boxing procedure that removes application of boxes to constants and constructors. Even though the de-boxing is not certified yet, before removing boxes we check if constant is applied to all logical argument (i.e. proofs or types) and constructors are fully applied. In this case, it is safe to remove these applications. *)
Time Run TemplateProgram
    (storage_def <- tmQuoteConstant "storage" false ;;
     storage_body <- opt_to_template storage_def.(cst_body) ;;
     ind <- tmQuoteInductive "msg" ;;
     ind_liq <- print_one_ind_body TT ind.(ind_bodies);;
     t1 <- toLiquidity TT inc_balance ;;
     t2 <- toLiquidity TT dec_balance ;;
     t3 <- toLiquidity TT counter ;;
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
                     ++ printWrapper "counter"
                     ++ nl ++ nl
                     ++ printMain) ;;
    tmDefinition "counter_extracted" res).

Print counter_extracted.

Redirect "counter.liq" Print counter_extracted.

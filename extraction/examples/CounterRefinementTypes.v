From Coq Require Import PeanoNat ZArith Notations Bool.

From MetaCoq.Template Require Import Loader.
From MetaCoq.Erasure Require Import Loader.

From ConCert Require Import MyEnv.
From ConCert.Embedding Require Import Notations CustomTactics.
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

Definition PREFIX := "coq_".

Module Type ZTheorems.
  Axiom lt_add_pos_r : forall n m : Z, 0 < n -> m < m + n.
End ZTheorems.

(** We use parameterised modules (functors) to isolate proof terms from the extracted parts. Otherwise type cheking and erasing is taking too long *)
Module CounterRefinmentTypes (ZT : ZTheorems).

  Definition storage := Z.

  Definition positive := {z : Z | 0 <? z}.

  Inductive msg :=
  | Inc (_ : Z)
  | Dec (_ : Z).

  Program Definition inc_counter (st : storage) (new_balance : positive) :
    {new_st : storage | st <? new_st} :=
    exist (st + proj1_sig new_balance) _.
  Next Obligation.
    destruct new_balance.
    unfold is_true in *. simpl.
    Zleb_ltb_to_prop. apply ZT.lt_add_pos_r. exact i.
  Qed.

  Definition dec_counter (st : storage) (new_balance : positive) :=
    st - proj1_sig new_balance.

  Definition my_bool_dec := Eval compute in bool_dec.

  Definition counter (msg : msg) (st : storage)
    : option (list SimpleActionBody * storage) :=
    match msg with
    | Inc i =>
      match (my_bool_dec (0 <? i) true) with
      | left h => Some ([], proj1_sig (inc_counter st (exist i h)))
      | right _ => None
      end
    | Dec i =>
      match (my_bool_dec (0 <? i) true) with
      | left h => Some ([], dec_counter st (exist i h))
      | right _ => None
      end
    end.

End CounterRefinmentTypes.

Module ZT : ZTheorems.
  Lemma lt_add_pos_r : forall n m : Z, 0 < n -> m < m + n.
  Proof. apply Z.lt_add_pos_r. Qed.
End ZT.

Module CRT := (CounterRefinmentTypes ZT).
Import CRT.


Definition local_def := local PREFIX.

(** A translation table for various constants we want to rename *)
Definition TT_rt : env string :=
  [  remap <% Z.add %> "addInt"
     ; remap <% Z.sub %> "subInt"
     ; remap <% Z.leb %> "leInt"
     ; remap <% Z.ltb %> "ltInt"
     ; remap <% Z %> "int"
     ; remap <% bool %> "bool"
     ; remap <% nat %> "address"
     ; remap <% option %> "option"
     ; remap <% proj1_sig %> "(fun x -> x)" (* this is a safe, but ad-hoc optimisation*)
     ; remap <% positive %> "int" (* this is again an ad-hoc optimisation *)
     ; ("Some", "Some")
     ; ("None", "None")
     ; ("true", "true")
     ; ("false", "false")
     ; ("exist", "exist")
     ; ("Z0" ,"0")
     ; ("nil", "[]")
     ; remap <% @fst %> "fst"
     ; remap <% @snd %> "snd"
     ; remap <% storage %> "storage"
     ; local_def <% storage %>
     ; local_def <% msg %>
     ; local_def <% my_bool_dec %>
     ; local_def <% inc_counter %>
     ; local_def <% dec_counter %>
  ].

(** exists becomes just a wrapper *)
Definition exists_def := "let exist a = a".

Quote Recursively Definition Counter := (counter).

(** We run the extraction procedure inside the [TemplateMonad]. It uses the certified erasure from [MetaCoq] and (so far uncertified) de-boxing procedure that remove redundant type abstractions and application of boxes *)
Time Run TemplateProgram
    (storage_def <- tmQuoteConstant "storage" false ;;
     storage_body <- opt_to_template storage_def.(cst_body) ;;
     sumbool_t <- tmQuoteInductive "sumbool" ;;
     sumbool_liq <- print_one_ind_body PREFIX TT sumbool_t.(ind_bodies);;
     ind <- tmQuoteInductive "msg" ;;
     ind_liq <- print_one_ind_body PREFIX TT_rt ind.(ind_bodies);;
     t1 <- toLiquidityEnv PREFIX TT_rt (Counter.1) inc_counter ;;
     t2 <- toLiquidityEnv PREFIX TT_rt (Counter.1) dec_counter ;;
     t3 <- toLiquidityEnv PREFIX TT_rt (Counter.1) my_bool_dec ;;
     t4 <- toLiquidityEnv PREFIX TT_rt (Counter.1) counter ;;
     res <- tmEval lazy
                  (prod_ops ++ nl ++ int_ops ++ nl ++ exists_def
                     ++ nl ++ nl
                     ++ "type storage = " ++ print_liq_type PREFIX TT_rt storage_body
                     ++ nl ++ nl
                     ++ sumbool_liq
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
                     ++ printWrapper (PREFIX ++ "counter")
                     ++ nl ++ nl
                     ++ printMain) ;;
    tmDefinition "counter_extracted_refinment_types" res).

Print counter_extracted_refinment_types.

(** * Extraction of a counter contract with dependent types (propositions) **)

(** A version of the counter contract that uses propositions to restrict the input.
    We also demonstrate how one can use the certifying eta-expansion to make sure
    that constants and constructors are applied to all logial arguments *)
From Coq Require Import PeanoNat ZArith Notations Bool.

From MetaCoq.Template Require Import Loader.
From MetaCoq.Erasure Require Import Loader.

From ConCert Require Import MyEnv.
From ConCert.Embedding Require Import Notations.
From ConCert.Execution Require Import Blockchain.
From ConCert.Extraction Require Import LiquidityExtract LPretty
     PreludeExt Common CertifyingEta Optimize OptimizeCorrectness Extraction.

From Coq Require Import List Ascii String.
Local Open Scope string_scope.

From MetaCoq.Template Require Import All.

Import ListNotations.
Import MonadNotation.

Open Scope Z.

Import Lia.

Definition PREFIX := "coq_".

Module Counter.


  Notation address := nat.

  Definition operation := unit.
  Definition storage := Z × address.

  Definition init (ctx : SimpleCallCtx) (setup : Z * address) : option storage :=
    let ctx' := ctx in (* prevents optimisations from removing unused [ctx]  *)
    Some setup.

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
    : option (list operation * storage) :=
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

  (** A version of the counter with [inc_balance] applied only partially.
      Requires eta-expansion for deboxing, because the last argument is logial. *)
  Definition counter_partially_applied (msg : msg) (st : storage)
    : option (list operation * storage) :=
  match msg with
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
    end.

End Counter.

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
  ; remap <% Z %> "int"
  ; remap <% nat %> "key_hash" (* type of account addresses*)
  ; remap <% operation %> "operation"
  ; remap <% @fst %> "fst"
  ; remap <% @snd %> "snd" ].

(** A translation table of constructors and some constants. The corresponding definitions will be extracted and renamed. *)
Definition TT_rename : list (string * string):=
  [ ("Some", "Some")
  ; ("None", "None")
  ; ("Z0" ,"0")
  ; ("nil", "[]")
  ; ("true", "true")
  ; (string_of_kername <%% storage %%>, "storage")  (* we add [storage] so it is printed without the prefix *) ].

Definition COUNTER_MODULE : LiquidityMod msg _ (Z × address) storage operation :=
  {| (* a name for the definition with the extracted code *)
     lmd_module_name := "liquidity_counter" ;

     (* definitions of operations on pairs and ints *)
     lmd_prelude := prod_ops ++ nl ++ int_ops;

     (* initial storage *)
     lmd_init := init ;

     (* no extra operations in [init] are required *)
     lmd_init_prelude := "" ;

     (* the main functionality *)
     lmd_receive := counter ;

     (* code for the entry point *)
     lmd_entry_point := printWrapper (PREFIX ++ "counter") ++ nl
                       ++ printMain |}.

(** We run the extraction procedure inside the [TemplateMonad].
    It uses the certified erasure from [MetaCoq] and the certified deboxing procedure
    that removes application of boxes to constants and constructors. *)

Time MetaCoq Run
     (t <- liquidity_extraction PREFIX TT_remap TT_rename COUNTER_MODULE ;;
      tmDefinition COUNTER_MODULE.(lmd_module_name) t
     ).

Print liquidity_counter.

(* Now we show how we can also eta expand using MetaCoq.
   There is a version of the counter above that it partially applied, and if we
   try to extract that extraction fails. *)

Definition COUNTER_PARTIAL_MODULE : LiquidityMod msg _ (Z × address) storage operation :=
  {| (* a name for the definition with the extracted code *)
     lmd_module_name := "liquidity_counter_partially_applied" ;

     (* definitions of operations on pairs and ints *)
     lmd_prelude := prod_ops ++ nl ++ int_ops;

     (* initial storage *)
     lmd_init := init ;

     (* no extra operations in [init] are required *)
     lmd_init_prelude := "" ;

     (* the main functionality *)
     lmd_receive := counter_partially_applied ;

     (* code for the entry point *)
     lmd_entry_point := printWrapper (PREFIX ++ "counter") ++ nl
                       ++ printMain |}.

Fail MetaCoq Run
     (liquidity_extraction PREFIX TT_remap TT_rename COUNTER_PARTIAL_MODULE).
(* The command has indeed failed with message:
   Erased environment is not expanded enough for dearging to be provably correct *)

(* However, Coq's metatheory already includes eta conversion as part of its TCB,
   so we can systematically eta expand the necessary terms and easily generate
   a proof that the new definition is equal to the old (by reflexivity). *)

(** Just a dummy definition to get the current module path *)
Definition anchor := fun x : nat => x.
Definition CURRENT_MODULE := Eval compute in <%% anchor %%>.1.

(** Running our eta-expansion procedure with MetaCoq *)
MetaCoq Run (counter_syn <- quote_recursively_body counter_partially_applied ;;
             tmDefinition "counter_partially_applied_syn" counter_syn;;
             (* eta-expand dedinitions in the environment *)
             Σexpanded <- eta_global_env_template
               check_masks_args
               CURRENT_MODULE
               counter_syn.1
               [<%% inc_balance %%>; <%% counter_partially_applied %%>]
               (fun kn => negb (eq_kername kn <%% inc_balance %%>) &&
                       negb (eq_kername kn <%% counter_partially_applied %%>))
               (fun kn => negb (eq_kername kn <%% inc_balance %%>) &&
                       negb (eq_kername kn <%% counter_partially_applied %%>));;
             tmDefinition "Σexpanded" Σexpanded).
(** [Σexpanded] contains expanded definitions *)

(** A proof generated by the eta-expansion procedure. *)
Check counter_partially_applied_expanded_correct.
(* counter_partially_applied_expanded_correct
     : counter_partially_applied = counter_partially_applied_expanded *)

(* Now we can extract this one successfully. *)

Definition COUNTER_PARTIAL_EXPANDED_MODULE : LiquidityMod msg _ (Z × address) storage operation :=
  {| (* a name for the definition with the extracted code *)
     lmd_module_name := "liquidity_counter_partially_applied_expanded" ;

     (* definitions of operations on pairs and ints *)
     lmd_prelude := prod_ops ++ nl ++ int_ops;

     (* initial storage *)
     lmd_init := init ;

     (* no extra operations in [init] are required *)
     lmd_init_prelude := "" ;

     (* the main functionality *)
     lmd_receive := counter_partially_applied_expanded ;

     (* code for the entry point *)
     lmd_entry_point := printWrapper (PREFIX ++ "counter") ++ nl
                       ++ printMain |}.

Time MetaCoq Run
     (t <- liquidity_extraction PREFIX TT_remap TT_rename COUNTER_PARTIAL_EXPANDED_MODULE ;;
      tmDefinition COUNTER_PARTIAL_EXPANDED_MODULE.(lmd_module_name) t
     ).

Print liquidity_counter_partially_applied_expanded.

(** We redirect the extraction result for later processing and compiling with the Liquidity compiler *)
Redirect "./extraction/examples/liquidity-extract/CounterDepCertifiedExtraction.liq" Compute liquidity_counter.

(** * Extraction of a counter contract with dependent types (propositions) *)

(** A version of the counter contract that uses propositions to restrict the input.
    We also demonstrate how one can use the certifying eta-expansion to make sure
    that constants and constructors are applied to all logical arguments *)

From MetaCoq.Common Require Import Kernames.
From MetaCoq.Template Require Import All.
From ConCert.Embedding Require Import Notations.
From ConCert.Embedding.Extraction Require Import PreludeExt.
From ConCert.Execution Require Import Blockchain.
From ConCert.Execution Require Import ResultMonad.
From ConCert.Extraction Require Import LiquidityExtract.
From ConCert.Extraction Require Import LiquidityPretty.
From ConCert.Extraction Require Import Common.
From MetaCoq.Erasure.Typed Require Import CertifyingEta.
From Coq Require Import ZArith.
From Coq Require Import Bool.
From Coq Require Import String.

Import MCMonadNotation.

Local Open Scope string_scope.
Open Scope Z.

Definition PREFIX := "coq_".

Module Counter.

  Definition address := nat.

  Definition operation := unit.
  Definition storage := Z × address.
  Definition Error : Type := nat.
  Definition default_error : Error := 1%nat.

  Definition init (ctx : SimpleCallCtx)
                  (setup : Z * address)
                  : result storage Error :=
    let ctx' := ctx in (* prevents optimizations from removing unused [ctx] *)
    Ok setup.

  Inductive msg :=
  | Inc (_ : Z)
  | Dec (_ : Z).

  Definition inc_balance (st : storage) (new_balance : Z)
               (p : (0 <=? new_balance) = true) : storage :=
    (st.1 + new_balance, st.2).


  Definition dec_balance (st : storage) (new_balance : Z)
             (p : (0 <=? new_balance) = true): storage :=
    (st.1 - new_balance, st.2).

  Definition my_bool_dec := Eval compute in bool_dec.

  Definition counter (msg : msg)
                     (st : storage)
                     : result (list operation * storage) Error :=
    match msg with
    | Inc i =>
      match (my_bool_dec (0 <=? i) true) with
      | left h =>
        Ok ([], inc_balance st i h)
      | right _ => Err default_error
      end
    | Dec i =>
      match (my_bool_dec (0 <=? i) true) with
      | left h => Ok ([], dec_balance st i h)
      | right _ => Err default_error
      end
    end.

  (** A version of the counter with [inc_balance] applied only partially.
      Requires eta-expansion for deboxing, because the last argument is logical. *)
  Definition counter_partially_applied (msg : msg)
                                       (st : storage)
                                       : result (list operation * storage) Error :=
  match msg with
    | Inc i =>
      match (my_bool_dec (0 <=? i) true) with
      | left h =>
        let f := inc_balance st i in
        Ok ([], f h)
      | right _ => Err default_error
      end
    | Dec i =>
      match (my_bool_dec (0 <=? i) true) with
      | left h => Ok ([], dec_balance st i h)
      | right _ => Err default_error
      end
    end.

End Counter.

Import Counter.

(** A translation table for definitions we want to remap. The corresponding top-level definitions will be *ignored* *)
Definition TT_remap : list (kername * string) :=
  [ remap <%% bool %%> "bool"
  ; remap <%% list %%> "list"
  ; remap <%% Amount %%> "tez"
  ; remap <%% address_coq %%> "address"
  ; remap <%% time_coq %%> "timestamp"
  ; remap <%% option %%> "option"
  ; remap <%% result %%> "result"
  ; remap <%% Z.add %%> "addInt"
  ; remap <%% Z.sub %%> "subInt"
  ; remap <%% Z.leb %%> "leInt"
  ; remap <%% Z %%> "int"
  ; remap <%% address %%> "key_hash" (* type of account addresses*)
  ; remap <%% operation %%> "operation"
  ; remap <%% @fst %%> "fst"
  ; remap <%% @snd %%> "snd" ].

(** A translation table of constructors and some constants. The corresponding definitions will be extracted and renamed. *)
Definition TT_rename : list (string * string) :=
  [ ("Some", "Some")
  ; ("None", "None")
  ; ("Ok", "Ok")
  ; ("Err", "Err")
  ; ("O", "0")
  ; ("Z0" ,"0")
  ; ("nil", "[]")
  ; ("true", "true")
  ; (String.to_string (string_of_kername <%% storage %%>), "storage") (* we add [storage] so it is printed without the prefix *) ].

Definition COUNTER_MODULE : LiquidityMod msg _ (Z × address) storage operation Error :=
  {| (* a name for the definition with the extracted code *)
     lmd_module_name := "liquidity_counter" ;

     (* definitions of operations on pairs and ints *)
     lmd_prelude := prod_ops ++ nl ++ int_ops ++ nl ++ result_def;

     (* initial storage *)
     lmd_init := init ;

     (* no extra operations in [init] are required *)
     lmd_init_prelude := "" ;

     (* the main functionality *)
     lmd_receive := counter ;

     (* code for the entry point *)
     lmd_entry_point := printWrapper (PREFIX ++ "counter") ++ nl
                       ++ printMain
  |}.

(** We run the extraction procedure inside the [TemplateMonad].
    It uses the certified erasure from [MetaCoq] and the certified deboxing procedure
    that removes application of boxes to constants and constructors. *)

Time MetaCoq Run
     (t <- liquidity_extraction PREFIX TT_remap TT_rename [] COUNTER_MODULE ;;
      tmDefinition (String.of_string COUNTER_MODULE.(lmd_module_name)) t
     ).

(* Print liquidity_counter. *)

(* Now we show how we can also eta expand using MetaCoq.
   There is a version of the counter above that it partially applied, and if we
   try to extract that extraction fails. *)

Definition COUNTER_PARTIAL_MODULE : LiquidityMod msg _ (Z × address) storage operation Error :=
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
     (liquidity_extraction PREFIX TT_remap TT_rename [] COUNTER_PARTIAL_MODULE).
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
             tmDefinition "counter_partially_applied_syn"%bs counter_syn;;
             (* eta-expand dedinitions in the environment *)
             Σexpanded <- eta_global_env_template
               (fun _ => None)
               true true
               CURRENT_MODULE
               counter_syn.1
               (KernameSet.add
                  <%% inc_balance %%>
                  (KernameSet.add
                     <%% counter_partially_applied %%>
                     KernameSet.empty))
               (fun kn => negb (eq_kername kn <%% inc_balance %%>) &&
                       negb (eq_kername kn <%% counter_partially_applied %%>));;
             tmDefinition "Σexpanded"%bs Σexpanded).
(** [Σexpanded] contains expanded definitions *)

(** A proof generated by the eta-expansion procedure. *)
(* Check ConCert_Examples_Counter_extraction_CounterDepCertifiedLiquidity_Counter_counter_partially_applied_expanded_convertible. *)
(* ConCert_Extraction_Tests_CounterDepCertifiedLiquidity_Counter_counter_partially_applied_expanded_convertible
     : counter_partially_applied =
       ConCert_Extraction_Tests_CounterDepCertifiedLiquidity_Counter_counter_partially_applied_expanded *)

(* Now we can extract this one successfully. *)

Definition COUNTER_PARTIAL_EXPANDED_MODULE : LiquidityMod msg _ (Z × address) storage operation Error :=
  {| (* a name for the definition with the extracted code *)
     lmd_module_name := "liquidity_counter_partially_applied_expanded" ;

     (* definitions of operations on pairs and ints *)
     lmd_prelude := prod_ops ++ nl ++ int_ops;

     (* initial storage *)
     lmd_init := init ;

     (* no extra operations in [init] are required *)
     lmd_init_prelude := "" ;

     (* the main functionality *)
     lmd_receive := ConCert_Examples_Counter_extraction_CounterDepCertifiedLiquidity_Counter_counter_partially_applied_expanded;

     (* code for the entry point *)
     lmd_entry_point := printWrapper (PREFIX ++ "counter") ++ nl
                       ++ printMain |}.

Time MetaCoq Run
     (t <- liquidity_extraction PREFIX TT_remap TT_rename [] COUNTER_PARTIAL_EXPANDED_MODULE ;;
      tmDefinition (String.of_string COUNTER_PARTIAL_EXPANDED_MODULE.(lmd_module_name)) t
     ).

(* Print liquidity_counter_partially_applied_expanded. *)

(** We redirect the extraction result for later processing and compiling with the Liquidity compiler *)
Redirect "../extraction/tests/extracted-code/liquidity-extract/CounterDepCertifiedLiquidity.liq" Compute liquidity_counter.

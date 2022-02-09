(** * Extraction of a counter contract with subset types to Liquidity and CameLIGO *)

(** The contract uses refinement types to specify some functional correctness properties *)

From Coq Require Import PeanoNat ZArith Notations Bool.

From MetaCoq.Template Require Import Loader.
From MetaCoq.Erasure Require Import Loader.

From ConCert Require Import MyEnv.
From ConCert.Embedding Require Import Notations CustomTactics.
From ConCert.Embedding.Extraction Require Import PreludeExt.
From ConCert.Extraction Require Import LPretty LiquidityExtract Common Extraction.
From ConCert.Extraction Require CameLIGOPretty CameLIGOExtract.
From ConCert.Execution Require Import Blockchain.

From Coq Require Import List Ascii String.
Local Open Scope string_scope.

From MetaCoq.Template Require Import All.

Import ListNotations.
Import MonadNotation.

Open Scope Z.

Import Lia.

Module CounterRefinementTypes.

  (** Enabling recursors for records allows for deriving [Serializable] instances. *)
  Set Nonrecursive Elimination Schemes.

  Notation address := nat.

  Definition Transaction := list ActionBody.
  Definition Transaction_none : Transaction := [].

  Definition storage := Z.

  Definition init (ctx : SimpleCallCtx) (setup : Z) : option storage :=
    let ctx_ := ctx in (* prevents optimisations from removing unused [ctx]  *)
    Some setup.

  Inductive msg := Inc (_ : Z) | Dec (_ : Z).

  Program Definition inc_counter (st : storage) (inc : {z : Z | 0 <? z}) :
    {new_st : storage | st <? new_st} :=
    st + inc.
  Next Obligation.
    intros st inc. unfold is_true in *.
    destruct inc;simpl.
    Zleb_ltb_to_prop. lia.
  Qed.

  Program Definition dec_counter (st : storage) (dec : {z : Z | 0 <? z}) :
    {new_st : storage | new_st <? st} :=
    st - dec.
  Next Obligation.
    intros st dec. unfold is_true in *.
    destruct dec;simpl.
    Zleb_ltb_to_prop. lia.
  Qed.

  Definition counter (msg : msg) (st : storage)
    : option (Transaction * storage) :=
    match msg with
    | Inc i =>
      match (bool_dec true (0 <? i)) with
      | left H => Some (Transaction_none, proj1_sig (inc_counter st (exist i (eq_sym H))))
      | right _ => None
      end
    | Dec i =>
      match (bool_dec true (0 <? i)) with
      | left h => Some (Transaction_none, proj1_sig (dec_counter st (exist i (eq_sym h))))
      | right _ => None
      end
    end.

End CounterRefinementTypes.

Import CounterRefinementTypes.

Section LiquidityExtractionSetup.

  Definition PREFIX := "coq_".
  
  (** [sig] and [exist] becomes just wrappers *)
  Definition sig_def := "type 'a sig_ = 'a".
  Definition exist_def := "let exist_ a = a".

  (** A translation table for definitions we want to remap. The corresponding top-level definitions will be *ignored* *)
  Definition TT_remap : list (kername * string) :=
    [ remap <%% bool %%> "bool"
    ; remap <%% list %%> "list"
    ; remap <%% Amount %%> "tez"
    ; remap <%% address_coq %%> "address"
    ; remap <%% time_coq %%> "timestamp"
    ; remap <%% option %%> "option"
    ; remap <%% Z.add %%> "addInt"
    ; remap <%% Z.sub %%> "subInt"
    ; remap <%% Z.leb %%> "leInt"
    ; remap <%% Z.ltb %%> "ltInt"
    ; remap <%% sig %%> "sig_" (* remapping [sig] to the wrapper *)
    ; remap <%% @proj1_sig %%> "(fun x -> x)" (* this is a safe, but ad-hoc optimisation*)
    ; remap <%% Z %%> "int"
    ; remap <%% nat %%> "key_hash" (* type of account addresses*)
    ; remap <%% Transaction %%> "operation list"
    ; remap <%% Transaction_none %%> "[]"
    ; remap <%% @fst %%> "fst"
    ; remap <%% @snd %%> "snd" ].

  (** A translation table of constructors and some constants. The corresponding definitions will be extracted and renamed. *)
  Definition TT_rename : list (string * string):=
    [ ("Some", "Some")
    ; ("None", "None")
    ; ("Z0" ,"0")
    ; ("nil", "[]")
    ; ("true", "true")
    ; ("exist", "exist_") (* remapping [exist] to the wrapper *)
    ; (string_of_kername <%% storage %%>, "storage")  (* we add [storage] so it is printed without the prefix *) ].

  Definition COUNTER_MODULE : LiquidityMod msg _ Z storage ActionBody :=
    {| (* a name for the definition with the extracted code *)
      lmd_module_name := "liquidity_counter" ;

      (* definitions of operations on pairs and ints *)
      lmd_prelude := concat nl [prod_ops;int_ops; sig_def; exist_def];

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

  Definition to_inline := [<%% bool_rect %%>; <%% bool_rec %%>].

End LiquidityExtractionSetup.


Time MetaCoq Run
     (t <- liquidity_extraction PREFIX TT_remap TT_rename to_inline COUNTER_MODULE ;;
      tmDefinition COUNTER_MODULE.(lmd_module_name) t
     ).

(** We redirect the extraction result for later processing and compiling with the Liquidity compiler*)
Redirect "examples/extracted-code/liquidity-extract/CounterSubsetTypes.liq"
MetaCoq Run (tmMsg liquidity_counter).


Module CameLIGOExtractionSetup.

  Import CameLIGOPretty CameLIGOExtract.

  (** Exposing a printing configuration for CameLIGO *)
  Existing Instance PrintConfAddModuleNames.PrintWithModuleNames.


  Definition init (ctx : ContractCallContext) (setup : Z) : option storage :=
    (* prevents optimisations from removing unused [ctx]
       TODO: override masks instead. *)
    let ctx_ := ctx in 
    Some setup.

  (** A translation table for definitions we want to remap. The corresponding top-level definitions will be *ignored* *)
  Definition TT_remap_ligo : list (kername * string) :=
    [
      remap <%% address %%> "address"
    ; remap <%% Z.add %%> "addInt"
    ; remap <%% Z.sub %%> "subInt"
    ; remap <%% Z.leb %%> "leInt"
    ; remap <%% Z.ltb %%> "ltInt"
    ; remap <%% Z %%> "int"
    ; remap <%% Transaction %%> "operation list"
    ].

  (** A translation table of constructors and some constants. The corresponding definitions will be extracted and renamed. *)
  Definition TT_rename_ligo : list (string * string):=
    [ ("true", "true")
    ; ("false", "false")
    ; ("Some", "Some")
    ; ("None", "None")
    ].

  Definition counter_wrapper (c : Chain) 
                             (ctx : ContractCallContext)
                             (s : storage)
                             (m : option msg) := 
    let c_ := c in
    let ctx_ := ctx in
    match m with
    | Some m => counter m s
    | None => None
    end.

 
  Definition COUNTER_MODULE_LIGO : CameLIGOMod msg _ Z storage ActionBody :=
    {| (* a name for the definition with the extracted code *)
      lmd_module_name := "cameligo_counter" ;

      (* definitions of operations on pairs and ints *)
      lmd_prelude := CameLIGOPrelude;
      (* initial storage *)
      lmd_init := init ;

      (* no extra operations in [init] are required *)
      lmd_init_prelude := "" ;

      (* the main functionality *)
      lmd_receive := counter_wrapper ;

      lmd_receive_prelude := "";
      (* code for the entry point *)
      lmd_entry_point := print_default_entry_point
                           <%% storage %%>
                           <%% counter_wrapper %%>
                           <%% msg %%> |}.

  (** We run the extraction procedure inside the [TemplateMonad].
      It uses the certified erasure from [MetaCoq] and the certified deboxing procedure
      that removes application of boxes to constants and constructors. *)

  Definition to_inline_ligo := [<%% bool_rect %%>; <%% bool_rec %%>; <%% @proj1_sig %%>].

  Time MetaCoq Run
  (CameLIGO_prepare_extraction to_inline_ligo TT_remap_ligo TT_rename_ligo [] "cctx_instance" COUNTER_MODULE_LIGO).

  Time Definition cameLIGO_counter := Eval vm_compute in cameligo_counter_prepared.

  MetaCoq Run (tmMsg cameLIGO_counter).

  Redirect "examples/extracted-code/cameligo-extract/CounterSubsetTypes.mligo"
  MetaCoq Run (tmMsg cameLIGO_counter).
    
End CameLIGOExtractionSetup.

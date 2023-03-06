(** * Extraction of a counter contract with subset types to Liquidity and CameLIGO *)

(** The contract uses refinement types to specify some functional correctness properties *)

From MetaCoq.Template Require Import All.
From ConCert.Embedding Require Import Notations.
From ConCert.Embedding.Extraction Require Import PreludeExt.
From ConCert.Extraction Require CameLIGOExtract.
From ConCert.Extraction Require CameLIGOPretty.
From ConCert.Extraction Require Import Common.
From ConCert.Utils Require Import Automation.
From ConCert.Execution Require Import Blockchain.
From ConCert.Execution Require Import ResultMonad.
From Coq Require Import ZArith.
From Coq Require Import Bool.
From Coq Require Import String.
From Coq Require Import Lia.

Import MCMonadNotation.

Local Open Scope string_scope.
Open Scope Z.

Module CounterRefinementTypes.

  (** Enabling recursors for records allows for deriving [Serializable] instances. *)
  Set Nonrecursive Elimination Schemes.

  Definition address := nat.

  Definition Transaction := list ActionBody.
  Definition Transaction_none : Transaction := [].

  Definition storage := Z.
  Definition Error : Type := nat.
  Definition default_error : Error := 1%nat.

  Definition init (ctx : SimpleCallCtx)
                  (setup : Z)
                  : result storage Error :=
    let ctx_ := ctx in (* prevents optimizations from removing unused [ctx] *)
    Ok setup.

  Inductive msg := Inc (_ : Z) | Dec (_ : Z).

  Program Definition inc_counter (st : storage) (inc : {z : Z | 0 <? z}) :
    {new_st : storage | st <? new_st} :=
    st + inc.
  Next Obligation.
    destruct inc;
    propify; lia.
  Qed.

  Program Definition dec_counter (st : storage) (dec : {z : Z | 0 <? z}) :
    {new_st : storage | new_st <? st} :=
    st - dec.
  Next Obligation.
    destruct dec;
    propify; lia.
  Qed.

  Definition counter (msg : msg)
                     (st : storage)
                     : result (Transaction * storage) Error :=
    match msg with
    | Inc i =>
      match (bool_dec true (0 <? i)) with
      | left H => Ok (Transaction_none, proj1_sig (inc_counter st (exist i (eq_sym H))))
      | right _ => Err default_error
      end
    | Dec i =>
      match (bool_dec true (0 <? i)) with
      | left h => Ok (Transaction_none, proj1_sig (dec_counter st (exist i (eq_sym h))))
      | right _ => Err default_error
      end
    end.

End CounterRefinementTypes.

Import CounterRefinementTypes.

Module CameLIGOExtractionSetup.

  Import CameLIGOPretty CameLIGOExtract.

  (** Exposing a printing configuration for CameLIGO *)
  #[local]
  Existing Instance PrintConfAddModuleNames.PrintWithModuleNames.


  Definition init (setup : Z) : result storage Error :=
    Ok setup.

  (** A translation table for definitions we want to remap. The corresponding top-level definitions will be *ignored* *)
  Definition TT_remap_ligo : list (kername * string) :=
    [ remap <%% address %%> "address"
    ; remap <%% Z.add %%> "addInt"
    ; remap <%% Z.sub %%> "subInt"
    ; remap <%% Z.leb %%> "leInt"
    ; remap <%% Z.ltb %%> "ltInt"
    ; remap <%% Z %%> "int"
    ; remap <%% Transaction %%> "operation list"
    ].

  Definition counter_wrapper (c : Chain)
                             (ctx : ContractCallContext)
                             (s : storage)
                             (m : option msg) :=
    let c_ := c in
    let ctx_ := ctx in
    match m with
    | Some m => counter m s
    | None => Err default_error
    end.


  Definition COUNTER_MODULE_LIGO : CameLIGOMod msg _ Z storage ActionBody Error :=
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
                           <%% msg %%>
    |}.

  (** We run the extraction procedure inside the [TemplateMonad].
      It uses the certified erasure from [MetaCoq] and the certified deboxing procedure
      that removes application of boxes to constants and constructors. *)

  Definition to_inline_ligo := [<%% bool_rect %%>; <%% bool_rec %%>; <%% @proj1_sig %%>].

  Time MetaCoq Run
  (CameLIGO_prepare_extraction to_inline_ligo TT_remap_ligo TT_rename_ctors_default [] "cctx_instance" COUNTER_MODULE_LIGO).

  Time Definition cameLIGO_counter := Eval vm_compute in cameligo_counter_prepared.

  Redirect "../extraction/tests/extracted-code/cameligo-extract/CounterSubsetTypes.mligo"
    MetaCoq Run (tmMsg (String.of_string cameLIGO_counter)).

End CameLIGOExtractionSetup.

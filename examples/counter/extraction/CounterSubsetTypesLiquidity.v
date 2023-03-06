(** * Extraction of a counter contract with subset types to Liquidity and CameLIGO *)

(** The contract uses refinement types to specify some functional correctness properties *)

From MetaCoq.Template Require Import All.
From ConCert.Embedding Require Import Notations.
From ConCert.Embedding.Extraction Require Import PreludeExt.
From ConCert.Extraction Require LiquidityPretty.
From ConCert.Extraction Require LiquidityExtract.
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
    now unfold is_true in *.
  Qed.

  Program Definition dec_counter (st : storage) (dec : {z : Z | 0 <? z}) :
    {new_st : storage | new_st <? st} :=
    st - dec.
  Next Obligation.
    now unfold is_true in *.
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

Section LiquidityExtractionSetup.

  Import LiquidityPretty.
  Import LiquidityExtract.

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
    ; remap <%% result %%> "result"
    ; remap <%% Z.add %%> "addInt"
    ; remap <%% Z.sub %%> "subInt"
    ; remap <%% Z.leb %%> "leInt"
    ; remap <%% Z.ltb %%> "ltInt"
    ; remap <%% sig %%> "sig_" (* remapping [sig] to the wrapper *)
    ; remap <%% @proj1_sig %%> "(fun x -> x)" (* this is a safe, but ad-hoc optimization*)
    ; remap <%% Z %%> "int"
    ; remap <%% address %%> "key_hash" (* type of account addresses*)
    ; remap <%% Transaction %%> "operation list"
    ; remap <%% Transaction_none %%> "[]"
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
    ; ("exist", "exist_") (* remapping [exist] to the wrapper *)
    ; (String.to_string (string_of_kername <%% storage %%>), "storage") (* we add [storage] so it is printed without the prefix *) ].

  Definition COUNTER_MODULE : LiquidityMod msg _ Z storage ActionBody Error :=
    {| (* a name for the definition with the extracted code *)
      lmd_module_name := "liquidity_counter" ;

      (* definitions of operations on pairs and ints *)
      lmd_prelude := concat nl [prod_ops; int_ops; sig_def; exist_def; result_def];

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

  Time MetaCoq Run
      (t <- liquidity_extraction PREFIX TT_remap TT_rename to_inline COUNTER_MODULE ;;
        tmDefinition (String.of_string COUNTER_MODULE.(lmd_module_name)) t
      ).

  (** We redirect the extraction result for later processing and compiling with the Liquidity compiler*)
  Redirect "../extraction/tests/extracted-code/liquidity-extract/CounterSubsetTypes.liq"
    MetaCoq Run (tmMsg (String.of_string liquidity_counter)).

End LiquidityExtractionSetup.

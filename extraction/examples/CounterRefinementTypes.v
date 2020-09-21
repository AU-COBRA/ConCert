From Coq Require Import PeanoNat ZArith Notations Bool.

From MetaCoq.Template Require Import Loader.
From MetaCoq.Erasure Require Import Loader.

From ConCert Require Import MyEnv.
From ConCert.Embedding Require Import Notations CustomTactics.
From ConCert.Extraction Require Import LPretty LiquidityExtract PreludeExt Common.
From ConCert.Execution Require Import Blockchain.

From Coq Require Import List Ascii String.
Local Open Scope string_scope.

From MetaCoq.Template Require Import All.

Import ListNotations.
Import MonadNotation.

Open Scope Z.

Import Lia.

Definition PREFIX := "coq_".

(** We use parameterised modules (functors) to isolate proof terms from the extracted parts. Otherwise type cheking and erasing is taking too long *)
Module CounterRefinmentTypes.

  (** Enabling recursors for records allows for deriving [Serializable] instances. *)
  Set Nonrecursive Elimination Schemes.

  Notation address := nat.

  Definition operation := ActionBody.
  Definition storage := Z.

  Definition init (ctx : SimpleCallCtx) (setup : Z) : option storage :=
    let ctx' := ctx in (* prevents optimisations from removing unused [ctx]  *)
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

  Definition my_bool_dec := Eval compute in bool_dec.

  Definition counter (msg : msg) (st : storage)
    : option (list operation * storage) :=
    match msg with
    | Inc i =>
      match (my_bool_dec (0 <? i) true) with
      | left h => Some ([], proj1_sig (inc_counter st (exist _ i h)))
      | right _ => None
      end
    | Dec i =>
      match (my_bool_dec (0 <? i) true) with
      | left h => Some ([], proj1_sig (dec_counter st (exist _ i h)))
      | right _ => None
      end
    end.

End CounterRefinmentTypes.

Import CounterRefinmentTypes.

(** [sig] and [exist] becomes just wrappers *)
Definition sig_def := "type 'a sig_ = 'a".
Definition exist_def := "let exist_ a = a".

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
  ; remap <% Z.ltb %> "ltInt"
  ; remap <% sig %> "sig_" (* remapping [sig] to the wrapper *)
  ; remap <% @proj1_sig %> "(fun x -> x)" (* this is a safe, but ad-hoc optimisation*)
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
  ; ("exist", "exist_") (* remapping [exist] to the wrapper *)
  ; (string_of_kername <%% storage %%>, "storage")  (* we add [storage] so it is printed without the prefix *) ].

Definition COUNTER_MODULE : LiquidityMod msg _ Z storage operation :=
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

Time MetaCoq Run
     (r <- tmQuoteRecTransp counter false;;
      b <- EnvCheck_to_template (erase_and_check_applied_no_wf_check r) ;;
      if (b : bool) then
        t <- liquitidy_extraction PREFIX TT_remap TT_rename COUNTER_MODULE ;;
        tmDefinition COUNTER_MODULE.(lmd_module_name) (wrap_in_delimeters t)
      else
        tmFail "Constructors or constants are not applied enough"
     ).

Print liquidity_counter.

(** We redirect the extraction result for later processing and compiling with the Liquidity compiler *)
Redirect "./extraction/examples/liquidity-extract/CounterRefinementTypes.liq" Compute liquidity_counter.

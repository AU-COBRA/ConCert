(** * Extraction of various contracts to CameLIGO *)

From Coq Require Import ZArith.
From Coq Require Import String.
From MetaCoq.Template Require Import All.
From ConCert.Embedding Require Import Notations.
From ConCert.Embedding.Extraction Require Import PreludeExt.
From ConCert.Embedding.Extraction Require SimpleBlockchainExt.
From ConCert.Extraction Require Import Common.
From ConCert.Extraction Require Import CameLIGOPretty.
From ConCert.Extraction Require Import CameLIGOExtract.
From ConCert.Execution Require Import Blockchain.
From ConCert.Execution Require Import ResultMonad.

Import MCMonadNotation.

Local Open Scope string_scope.
Open Scope Z.

#[local]
Existing Instance PrintConfShortNames.PrintWithShortNames.

Module Counter.

  (** Enabling recursors for records allows for deriving [Serializable] instances. *)
  Set Nonrecursive Elimination Schemes.

  (** The definitions in this section are generalized over the [ChainBase] that specifies the type of addresses and which properties such a type must have *)
  Definition address := nat.

  Definition operation := ActionBody.
  Definition storage := Z × address.

  Definition Error : Type := nat.
  Definition default_error : Error := 1%nat.

  Definition init (setup : Z * address) : result storage Error :=
    Ok setup.

  Inductive msg :=
  | Inc (_ : Z)
  | Dec (_ : Z).

  Definition inc_balance (st : storage) (new_balance : Z) :=
    (st.1 + new_balance, st.2).

  Definition dec_balance (st : storage) (new_balance : Z) :=
    (st.1 - new_balance, st.2).

  Definition counter_inner (msg : msg)
                           (st : storage)
                           : result (list operation * storage) Error :=
    match msg with
    | Inc i =>
      if (0 <=? i) then
        Ok ([],inc_balance st i)
      else Err default_error
    | Dec i =>
      if (0 <=? i) then
        Ok ([],dec_balance st i)
      else Err default_error
    end.

  Definition counter (c : Chain) (ctx : ContractCallContext) st msg :=
    (* TODO: we should override masks instead *)
    (* avoid erasing c and ctx arguments *)
    let c_ := c in
    let ctx_ := ctx in
    match msg with
    | Some msg => counter_inner msg st
    | None => Err default_error
    end.

  Definition LIGO_COUNTER_MODULE : CameLIGOMod msg _ (Z × address) storage operation Error :=
    {| (* a name for the definition with the extracted code *)
        lmd_module_name := "cameLIGO_counter" ;

        (* and a test address *)
        lmd_prelude := CameLIGOPrelude ++ nl
                       ++ "let test_account : address = (""tz1KqTpEZ7Yob7QbPE4Hy4Wo8fHG8LhKxZSx"" : address)";

        (* initial storage *)
        lmd_init := init ;

        (* no extra operations in [init] are required *)
        lmd_init_prelude := "" ;

        (* the main functionality *)
        lmd_receive_prelude := "";

        lmd_receive := counter;

        (* code for the entry point *)
        lmd_entry_point :=
          CameLIGOPretty.printMain "counter" "msg" "storage"
    |}.

End Counter.

Section CounterExtraction.
  Import Counter.
  (** A translation table for definitions we want to remap. The corresponding top-level definitions will be *ignored* *)
  Definition TT_remap_counter : list (kername * String.string) :=
    [ remap <%% Z %%> "int"
    ; remap <%% Z.add %%> "addInt"
    ; remap <%% Z.sub %%> "subInt"
    ; remap <%% Z.mul %%> "multInt"
    ; remap <%% Z.leb %%> "leInt"
    ; remap <%% Z.ltb %%> "ltInt"
    ; remap <%% Z.eqb %%> "eqInt"
    ; remap <%% Z.gtb %%> "gtbInt"
    ; remap <%% Z.even %%> "evenInt"
    ; remap <%% Z.abs_N %%> "abs"
    ; remap <%% address_coq %%> "address"
    ; remap <%% time_coq %%> "timestamp"
    ; remap <%% address %%> "address"
    ; remap <%% operation %%> "operation"
    ].

  (** We run the extraction procedure inside the [TemplateMonad]. *)
  (*  It uses the certified erasure from [MetaCoq] and the certified deboxing procedure *)
  (*  that removes application of boxes to constants and constructors. *)

  (** NOTE: running computations inside [TemplateMonad] is quite slow. That's why we comment out this code and use a different way below *)

  (* Time MetaCoq Run *)
  (*   (t <- CameLIGO_extract [] TT_remap_counter [] [] CameLIGO_call_ctx LIGO_COUNTER_MODULE ;; *)
  (*     tmDefinition LIGO_COUNTER_MODULE.(lmd_module_name) t). *)


  (*  If we first prepare the environment for erasure in [TemplateMonad] *)
  (*  and run erasure/printing outside of it, it works ~4 times faster for this example *)

  (** This command adds [cameLIGO_counter_prepared] to the environment, *)
  (*  which can be evaluated later *)
  Time MetaCoq Run
       (CameLIGO_prepare_extraction [] TT_remap_counter TT_rename_ctors_default [] "cctx_instance" LIGO_COUNTER_MODULE).

  Time Definition cameLIGO_counter_1 := Eval vm_compute in cameLIGO_counter_prepared.

  (** We redirect the extraction result for later processing and compiling with the CameLIGO compiler *)
  Redirect "../extraction/tests/extracted-code/cameligo-extract/CounterCertified.mligo"
  MetaCoq Run (tmMsg (String.of_string cameLIGO_counter_1)).

End CounterExtraction.

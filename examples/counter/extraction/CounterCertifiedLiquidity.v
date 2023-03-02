(** * Extraction of a simple counter contract *)

From MetaCoq.Template Require Import All.
From ConCert.Embedding Require Import Notations.
From ConCert.Embedding.Extraction Require Import PreludeExt.
From ConCert.Extraction Require Import LiquidityPretty.
From ConCert.Extraction Require Import LiquidityExtract.
From ConCert.Extraction Require Import Common.
From ConCert.Utils Require Import Automation.
From ConCert.Execution Require Import Serializable.
From ConCert.Execution Require Import Blockchain.
From ConCert.Execution Require Import ResultMonad.
From Coq Require Import String.
From Coq Require Import Lia.
From Coq Require Import ZArith.

Import MCMonadNotation.

Local Open Scope string_scope.
Open Scope Z.

Definition PREFIX := "".

Module Counter.

  (** Enabling recursors for records allows for deriving [Serializable] instances. *)
  Set Nonrecursive Elimination Schemes.

  (** The definitions in this section are generalized over the [ChainBase] that specifies the type of addresses and which properties such a type must have *)
  Definition address := nat.

  Definition operation := ActionBody.
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

  Definition inc_balance (st : storage) (new_balance : Z) : storage :=
    (st.1 + new_balance, st.2).

  Definition dec_balance (st : storage) (new_balance : Z) : storage :=
    (st.1 - new_balance, st.2).

  Definition counter (msg : msg)
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



  (** These definitions define a contract in a format required by the execution framework. Note that these definitions will not be used for extraction. We extract the definitions above instead. *)
  Definition counter_init (ch : Chain) (ctx : ContractCallContext) :=
    init_wrapper init ch ctx.

  Definition counter_receive (chain : Chain)
                             (ctx : ContractCallContext)
                             (st : storage)
                             (msg : option msg)
                             : result (storage * list ActionBody) Error :=
    match msg with
    | Some m => match counter m st with
              | Ok res => Ok (res.2,res.1)
              | Err e => Err e
              end
    | None => Err default_error
    end.

  (** Deriving the [Serializable] instances for the state and for the messages *)
  Global Instance Msg_serializable : Serializable msg :=
    Derive Serializable msg_rect<Inc, Dec>.

  (** A contract instance used by the execution framework *)
  Definition CounterContract :=
    build_contract counter_init counter_receive.

End Counter.

Import Counter.

Lemma inc_correct state n m :
  0 <= m ->
  state.1 = n ->
  exists new_state, counter (Inc m) state = Ok ([],new_state)
                    /\ new_state.1 = (n + m)%Z.
Proof.
  intros Hm Hn.
  eexists.
  split.
  - simpl.
    destruct ?; propify; auto; lia.
  - simpl.
    congruence.
Qed.

Lemma dec_correct state n m :
  0 <= m ->
  state.1 = n ->
  exists new_state, counter (Dec m) state = Ok ([],new_state)
                    /\ new_state.1 = (n - m)%Z.
Proof.
  intros Hm Hn.
  eexists.
  split.
  - simpl.
    destruct ?; propify; auto; lia.
  - simpl.
    congruence.
Qed.

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
Definition TT_rename :=
  [ ("Some", "Some")
  ; ("None", "None")
  ; ("Ok", "Ok")
  ; ("Err", "Err")
  ; ("O", "0")
  ; ("Z0" ,"0")
  ; ("nil", "[]") ].

(** We run the extraction procedure inside the [TemplateMonad].
    It uses the certified erasure from [MetaCoq] and the certified deboxing procedure
    that removes application of boxes to constants and constructors. *)

Time MetaCoq Run
     (t <- liquidity_extraction PREFIX TT_remap TT_rename [] COUNTER_MODULE ;;
      tmDefinition (String.of_string COUNTER_MODULE.(lmd_module_name)) t).

(* Print liquidity_counter. *)

(** We redirect the extraction result for later processing and compiling with the Liquidity compiler *)
Redirect "../extraction/tests/extracted-code/liquidity-extract/CounterCertifiedLiquidity.liq" Compute liquidity_counter.

From ConCert.Execution Require Blockchain.
From ConCert.Utils Require Import RecordUpdate.

Require Import Monads.
Require Import Extras.
Require Import Containers.
Require Import Automation.
Require Import Serializable.
Require Import Blockchain.

From ConCert.Extraction Require Import Common.
From ConCert.Extraction Require Import ConcordiumExtract.
From ConCert.Extraction Require Import ResultMonad.
From ConCert.Extraction Require Import RustExtract.
From Coq Require Import Bool.
From Coq Require Import List.
From Coq Require Import String.
From Coq Require Import ZArith.
From MetaCoq.Template Require Import All.

Import MonadNotation.
Import Printing.

Import Blockchain.

Open Scope string.
Open Scope Z.

Module SimpleCounter.
  Context {BaseTypes : ChainBase}.
  Definition State := Z.

  Inductive Msg :=
  | Inc (i : Z)
  | Dec (i : Z).

  Definition counter_receive (chain : Chain) (ctx : ContractCallContext)
             (state : State) (msg : Msg) : option (State * list ActionBody)
    := match msg with
       | Inc i => if (0 <? i) then Some (state + i, [])
                  else None
       | Dec i => if (0 <? i) then Some (state - i, [])
                  else None
       end.

  Definition counter_init (chain : Chain) (ctx : ContractCallContext) (init_value : Z)
    : option State := Some 0.


  Import Lia.

  Lemma counter_correct {chain ctx msg} (prev_state next_state : Z) :
  counter_receive chain ctx prev_state msg = Some (next_state, []) ->
  match msg with
  | Inc n =>  next_state > prev_state
             /\ next_state = prev_state + n
  | Dec n => next_state < prev_state
             /\ next_state = prev_state - n
  end.
  Proof.
    intros H.
    all : destruct msg;cbn in *.
    all : destruct (0 <? i) eqn:Hz;inversion H;cbn in *.
    all : rewrite Z.ltb_lt in *;split;auto;lia.
  Qed.

  Global Instance Msg_serializable : Serializable Msg :=
    Derive Serializable Msg_rect<Inc, Dec>.

  Definition counter_receive_wrapper (chain : Chain) (ctx : ContractCallContext)
             (state : State) (msg : option Msg) : option (State * list ActionBody)
    := match msg with
       | Some m => counter_receive chain ctx state m
       | None => None
       end.


  (** The counter contract *)
  Definition counter_contract : Contract Z Msg State :=
    build_contract counter_init counter_receive_wrapper.

End SimpleCounter.

Definition COUNTER_MODULE : ConcordiumMod _ _ :=
  {| concmd_contract_name := "counter";
     concmd_init := SimpleCounter.counter_init;
     concmd_receive := SimpleCounter.counter_receive_wrapper;
     concmd_extra := []; |}.

Instance RustConfig : RustPrintConfig :=
    {| term_box_symbol := "()";
       type_box_symbol := "()";
       any_type_symbol := "()";
       print_full_names := false |}.


(* Redirect "SimpleCounter.rs" *)
MetaCoq Run (concordium_extraction
               COUNTER_MODULE
               (ConcordiumRemap.build_remaps
                  (ConcordiumRemap.remap_arith ++ ConcordiumRemap.remap_blockchain_consts)
                  []
                  (ConcordiumRemap.remap_blockchain_inductives
                     ++ ConcordiumRemap.remap_std_types))
               (fun kn => eq_kername <%% bool_rec %%> kn
                          || eq_kername <%% bool_rect %%> kn)).

(** * Extraction of Escrow to CameLIGO and liquidity *)

From MetaCoq.Template Require Import All.
From ConCert.Embedding.Extraction Require Import SimpleBlockchainExt.
From ConCert.Execution Require Import Blockchain.
From ConCert.Execution Require Import ResultMonad.
From ConCert.Execution Require Monad.
From ConCert.Examples.Escrow Require Import Escrow.
From ConCert.Extraction Require Import Common.
From ConCert.Extraction Require CameLIGOPretty.
From ConCert.Extraction Require CameLIGOExtract.
From Coq Require Import String.
From Coq Require Import ZArith_base.

Local Open Scope string_scope.

Definition escrow_init_wrapper (cctx : ContractCallContext)
                               (s : Setup * Chain)
                               : result State Error :=
  Escrow.init (snd s) cctx (fst s).

Definition ligo_init (s : Address * Setup * nat)
                     : result State Error :=
  let seller := s.1.1 in
  let setup := s.1.2 in
  let curr_slot := s.2 in
  let buyer := setup_buyer setup in
  if (buyer =? seller)%address then Err default_error
  else Ok {| last_action := curr_slot;
               next_step := buyer_commit;
               seller := seller;
               buyer := buyer;
               seller_withdrawable := 0;
               buyer_withdrawable := 0 |}.

Lemma escrow_init_eq_ligo_init cctx s :
  (* The contract should be deployed with non-zero even amount *)
  (ctx_amount cctx =? 0 = false)%Z ->
  Z.even (ctx_amount cctx) ->
  escrow_init_wrapper cctx s = ligo_init (cctx.(ctx_from),s.1, s.2.(current_slot)).
Proof.
  intros Hamount Heven.
  unfold escrow_init_wrapper,init, ligo_init. cbn.
  rewrite Hamount.
  now destruct (_ =? _)%address; destruct (Z.even _).
Qed.

Definition escrow_receive (c : Chain)
                          (cctx : ContractCallContext)
                          (s : State)
                          (msg : option Msg)
                          : result (list ActionBody * State) Error :=
  match Escrow.receive c cctx s msg with
  | Ok (s, acts) => Ok (acts, s)
  | Err e => Err e
  end.


Module EscrowCameLIGOExtraction.
  Import CameLIGOExtract.
  Import CameLIGOPretty.
  #[local]
  Existing Instance PrintConfShortNames.PrintWithShortNames.

  (** A translation table of constructors and some constants. The corresponding definitions will be extracted and renamed. *)
  Definition TT_rename_ligo : list (string * string) :=
    [ ("true", "true")
    ; ("false", "false")
    ; ("tt", "()")
    ].

  Definition TT_remap_ligo : list (kername * string) :=
    [ remap <%% subAmountOption %%> "subTez" ].

  Definition ESCROW_MODULE_LIGO : CameLIGOMod Msg ContractCallContext _ State ActionBody Error :=
    {| (* a name for the definition with the extracted code *)
      lmd_module_name := "cameligo_escrow" ;

      (* definitions of operations on numbers, call context, etc. *)
      lmd_prelude := CameLIGOPrelude;

      (* initial storage *)
      lmd_init := ligo_init ;

      (* no extra operations in [init] are required *)
      lmd_init_prelude := "";

      (* the main functionality *)
      lmd_receive := escrow_receive ;

      lmd_receive_prelude := "";
      (* code for the entry point *)
      lmd_entry_point :=
        printMain "escrow_receive" "msg" "state"
    |}.

  Definition to_inline : list kername :=
    [ <%% @ConCert.Execution.ResultMonad.Monad_result %%>
    ; <%% @Monad.bind %%>
    ; <%% @Monad.ret %%>
    ; <%% @Monad.lift %%>
    ; <%% bool_rect %%>
    ; <%% bool_rec %%>
    ; <%% option_map %%>
    ; <%% @Extras.with_default %%>

    ; <%% @setter_from_getter_State_last_action %%>
    ; <%% @setter_from_getter_State_next_step %%>
    ; <%% @setter_from_getter_State_seller %%>
    ; <%% @setter_from_getter_State_buyer %%>
    ; <%% @setter_from_getter_State_seller_withdrawable %%>
    ; <%% @setter_from_getter_State_buyer_withdrawable %%>

    ; <%% default_error %%>
    ].

  Time MetaCoq Run
    (CameLIGO_prepare_extraction to_inline TT_remap_ligo
      TT_rename_ligo [] "cctx_instance" ESCROW_MODULE_LIGO).

  Time Definition cameLIGO_escrow := Eval vm_compute in cameligo_escrow_prepared.

  Redirect "../extraction/tests/extracted-code/cameligo-extract/EscrowExtract.mligo"
    MetaCoq Run (tmMsg (String.of_string cameLIGO_escrow)).

End EscrowCameLIGOExtraction.

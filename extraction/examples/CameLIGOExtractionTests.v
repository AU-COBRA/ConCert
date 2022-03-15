(** * Extraction of various contracts to CameLIGO *)

From Coq Require Import Lia.
From Coq Require Import List.
From Coq Require Import String.
From MetaCoq.Template Require Import All.
From ConCert.Extraction Require Import Common.
From ConCert.Extraction Require Import CameLIGOPretty.
From ConCert.Extraction Require Import CameLIGOExtract.

Import MonadNotation.

Local Open Scope string_scope.

Existing Instance PrintConfShortNames.PrintWithShortNames.

Definition bindOptCont {A B} (a : option A) (f : A -> option B) : option B :=
  match a with
  | Some a => f a
  | None => None
  end.

Module SafeHead.
  (** This module shows how one can extract programs containing [False_rect] *)

  Open Scope list.
  Open Scope nat.

  (** We cannot make [safe_head] polymoprhic due to CameLIGO restrictions *)
  Program Definition safe_head (l : list nat) (non_empty : List.length l > 0) : nat :=
    match l as l' return l' = l -> nat  with
    | [] => (* this is an impossible case *)
      (* NOTE: we use [False_rect] to have more control over the extracted code. *)
      (* Leaving a hole for the whole branch potentially leads to polymoprhic *)
      (* definitions in the extracted code and type like [eq], since we would have to leave the whole goal branch transparent (use [Defined] instead of [Qed] ). *)
      (* In this case, one has to inspect the extracted code and inline such definitions *)
      fun _ => False_rect _ _
    | hd :: tl => fun _ => hd
    end eq_refl.
  Next Obligation.
    intros. subst. inversion non_empty.
  Qed.

  Program Definition head_of_list_2 (xs : list nat) := safe_head (0 :: 0 :: xs)  _.
  Next Obligation.
    intros. cbn. lia.
  Qed.

  (** We inline [False_rect] and [False_rec] to make sure that no polymoprhic definitions are left *)
  Definition safe_head_inline :=
    [<%% False_rect %%>; <%% False_rec %%>].

  Definition TT_consts := [ remap <%% @hd_error %%> "List.head_opt" ].
  Definition TT_ctors := [("O","0n")].

  Definition harness : string :=
    "let main (st : unit * nat option) : operation list * (nat option)  = (([]: operation list), Some (head_of_list_2 ([] : nat list)))".

    Time MetaCoq Run
         (t <- CameLIGO_extract_single
                safe_head_inline
                TT_consts
                (TT_ctors ++ TT_rename_ctors_default)
                ""
                harness
                head_of_list_2 ;;
    tmDefinition "cameligo_safe_head" t).

    (** Extraction results in fully functional CameLIGO code *)
    Redirect "examples/extracted-code/cameligo-extract/SafeHead.mligo"
    MetaCoq Run (tmMsg cameligo_safe_head).

End SafeHead.

From Coq Require Import String.
From Coq Require Import List.
From MetaCoq.Template Require Import All.

Import ListNotations.
Import MonadNotation.

Open Scope string.

(** Generation of string constants using MetaCoq *)
Fixpoint mkNames (prefix : string) (ns : list string) (postfix : string) :=
  match ns with
  | [] => tmPrint "Done."
  | n :: ns' => n' <- tmEval all (prefix ++ n ++ postfix)%string ;;
                  str <- tmQuote n';;
                  tmMkDefinition n str;;
                  mkNames prefix ns' postfix
  end.

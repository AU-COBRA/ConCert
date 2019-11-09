From Coq Require Import String List.
From MetaCoq.Template Require Import All.

Import ListNotations.
Import MonadNotation.

(** Generation of string constants using MetaCoq *)
Fixpoint mkNames (ns : list string) (postfix : string) :=
  match ns with
  | [] => tmPrint "Done."
  | n :: ns' => n' <- tmEval all (n ++ postfix)%string ;;
                  str <- tmQuote n';;
                  tmMkDefinition n str;;
                  mkNames ns' postfix
  end.

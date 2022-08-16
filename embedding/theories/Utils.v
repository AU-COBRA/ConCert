From MetaCoq.Template Require Import All.
From Coq Require Import String.
From Coq Require Import List.

Import ListNotations.
Import MCMonadNotation.

Module TCString := bytestring.String.

Open Scope string.

(** Generation of string constants using MetaCoq *)
Fixpoint mkNames (prefix : string) (ns : list string) (postfix : string) :=
  match ns with
  | [] => tmPrint "Done."%bs
  | n :: ns' => n' <- tmEval all (prefix ++ n ++ postfix)%string ;;
                  str <- tmQuote n';;
                  tmMkDefinition (TCString.of_string n) str;;
                  mkNames prefix ns' postfix
  end.

From ConCert.Execution Require Import Blockchain.
From ConCert.Execution Require Import Serializable.
From ConCert.Execution Require Import Containers.
From ConCert.Execution Require Import Congress.
From ConCert.Extraction Require Import Certified.
From ConCert Require Import MyEnv.

From Coq Require Import List.
From Coq Require Import String.
From Coq Require Import ZArith.

From MetaCoq.SafeChecker Require Import Loader PCUICSafeChecker SafeTemplateChecker.
From MetaCoq.Template Require Import All.
From MetaCoq.Erasure Require Import Debox Loader SafeTemplateErasure EAst EAstUtils ETyping.

Import ListNotations.
Import MonadNotation.

Record PrettyPrinterState :=
  {
    indent : nat;
    output : string
  }.

Definition PrettyPrinter A := PrettyPrinterState -> (string + A * PrettyPrinterState).

Instance Monad_PrettyPrinter : Monad PrettyPrinter :=
  {| ret _ a pps := inr (a, pps);
     bind _ _ m f pps :=
       match m pps with
       | inl err => inl err
       | inr (a, pps) => f a pps
       end |}.

Definition printer_fail (str : string) : PrettyPrinter unit :=
  fun pps => inl str.

(*
Inductive PrettyPrinter A :=
| pp_error (msg : string)
| pp_print (f : PrettyPrinterState -> string + A * PrettyPrinterState).

Arguments pp_print {_}.
Arguments pp_error {_}.

Instance Monad_PrettyPrinter : Monad PrettyPrinter :=
  {| ret _ a := pp_print (fun pps => inr (a, pps));
     bind _ _ m f :=
       match m with
       | pp_error msg => pp_error msg
       | pp_print h =>
         pp_print
           (fun pps =>
              match h pps with
              | inl msg => inl msg
              | inr (a, pps) =>
                match f a with
                | pp_error msg => inl msg
                | pp_print g => g pps
                end
              end)
       end |}.
*)

(*
Definition State T A := T -> A * T.

Instance Monad_State {T} : Monad (State T) :=
  {| ret _ x t := (x, t);
     bind _ _ a f x := let (t, x) := a x in f t x |}.

Definition get_state {T} : State T T :=
  fun t => (t, t).

Definition set_state {T} (t : T) : State T unit :=
  fun _ => (tt, t).

Definition update_state {T} (f : T -> T) : State T unit :=
  fun t => (tt, f t).

Definition PrettyPrinter := State PrettyPrinterState.
*)

Definition finish_print {A} (pp : PrettyPrinter A) : string + A * string :=
  match pp {| indent := 0; output := "" |} with
  | inl err => inl err
  | inr (a, pps) => inr (a, output pps)
  end.

Definition update_indent (f : nat -> nat) : PrettyPrinter unit :=
  fun pps => inr (tt, {| indent := f (indent pps); output := output pps |}).

Definition inc_indent : PrettyPrinter unit :=
  update_indent S.

Definition dec_indent : PrettyPrinter unit :=
  update_indent pred.

Local Open Scope string.
Definition update_output (f : string -> string) : PrettyPrinter unit :=
  fun pps => inr (tt, {| indent := indent pps; output := f (output pps) |}).

Definition append (s : string) : PrettyPrinter unit :=
  update_output (fun o => o ++ s).

Definition append_indent : PrettyPrinter unit :=
  fun pps => inr (tt,
                  {| indent := indent pps;
                     output := output pps ++ concat "" (repeat "  " (indent pps)) |}).

Definition append_line (s : string) : PrettyPrinter unit :=
  update_output (fun o => o ++ s ++ nl).

Local Open Scope list.
Fixpoint print_term (Γ : context) (t : term) : PrettyPrinter unit :=
  match t with
  | tBox _ => printer_fail "tBox"
  | tRel _ => printer_fail "tRel"
  | tVar ident => printer_fail ("tVar " ++ ident)
  | tEvar _ => printer_fail "unexpected evar"
  | tLambda


Definition erase_check_debox_all_print
           (TT : env string)
           (decl_name : string)
           (tys : list Ast.term)
           (p : Ast.program) : string :=
  let p := fix_program_universes p in
  let deboxed := erase_check_debox_all TT p in
  deboxed.

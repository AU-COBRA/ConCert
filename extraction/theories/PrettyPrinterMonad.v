From ConCert.Extraction Require Import ResultMonad.
From Coq Require Import Ascii.
From Coq Require Import List.
From Coq Require Import String.
From MetaCoq Require Import monad_utils.
From MetaCoq Require Import MCString.
From MetaCoq.PCUIC Require Import PCUICAst.
From MetaCoq.SafeChecker Require Import PCUICSafeChecker.
From MetaCoq.Template Require Import BasicAst.

Import ListNotations.
Import MonadNotation.
Local Open Scope string.

Record PrettyPrinterState :=
  {
    indent_stack : list nat;
    used_names : list ident;
    output : string;
  }.

Definition PrettyPrinter A := PrettyPrinterState -> result (A * PrettyPrinterState) string.

Instance Monad_PrettyPrinter : Monad PrettyPrinter :=
  {| ret _ a pps := Ok (a, pps);
     bind _ _ m f pps :=
       match m pps with
       | Ok (a, pps) => f a pps
       | Err err => Err err
       end |}.

Definition printer_fail {A} (str : string) : PrettyPrinter A :=
  fun pps => Err (str ++ nl ++ "failed after printing" ++ nl ++ output pps).

Definition finish_print {A} (pp : PrettyPrinter A) : result (A * string) string :=
  '(a, pps) <- pp {| indent_stack := [];
                     used_names := [];
                     output := "" |};;
  ret (a, output pps).

Definition get_indent : PrettyPrinter nat :=
  fun pps => Ok (hd 0 (indent_stack pps), pps).

Definition update_indent (f : list nat -> list nat) : PrettyPrinter unit :=
  fun pps => Ok (tt, {| indent_stack := f (indent_stack pps);
                        used_names := used_names pps;
                        output := output pps |}).

Definition push_indent (n : nat) : PrettyPrinter unit :=
  update_indent (cons n).

Definition pop_indent : PrettyPrinter unit :=
  update_indent (@tl nat).

Definition get_used_names : PrettyPrinter (list ident) :=
  fun pps => Ok (used_names pps, pps).

Definition update_used_names (f : list ident -> list ident) : PrettyPrinter unit :=
  fun pps => Ok (tt, {| indent_stack := indent_stack pps;
                        used_names := f (used_names pps);
                        output := output pps |}).

Definition push_use (n : ident) : PrettyPrinter unit :=
  update_used_names (cons n).

Definition pop_use : PrettyPrinter unit :=
  update_used_names (@tl string).

Definition is_newline (c : ascii) : bool :=
  match c with
  | "010"%char => true
  | _ => false
  end.

Definition last_line_length (s : string) : nat :=
  (fix f (s : string) (result : nat) :=
     match s with
     | EmptyString => result
     | String c s =>
       if is_newline c then
         f s 0
       else
         f s (S result)
     end) s 0.

Definition get_current_line_length : PrettyPrinter nat :=
  fun pps => Ok (last_line_length (output pps), pps).

Definition update_output (f : string -> string) : PrettyPrinter unit :=
  fun pps => Ok (tt, {| indent_stack := indent_stack pps;
                        used_names := used_names pps;
                        output := f (output pps) |}).

Definition append (s : string) : PrettyPrinter unit :=
  update_output (fun o => o ++ s).

Definition append_nl : PrettyPrinter unit := append nl.

Definition append_indent : PrettyPrinter unit :=
  indent <- get_indent;;
  append (concat "" (repeat " " indent)).

Definition append_nl_and_indent : PrettyPrinter unit :=
  append_nl;; append_indent.

Definition fresh_name (name : ident) (extra_used : list ident) : PrettyPrinter ident :=
  used <- get_used_names;;
  let used := (extra_used ++ used)%list in
  if existsb (String.eqb name) used then
    (fix f n i :=
       match n with
       | 0 => ret "unreachable"
       | S n =>
         let numbered_name := (name ++ string_of_nat i)%string in
         if existsb (String.eqb numbered_name) used then
           f n (S i)
         else
           ret numbered_name
       end) (S (List.length used)) 2
  else
    ret name.

Definition string_of_env_error Σ e :=
  match e with
  | IllFormedDecl s e =>
    "IllFormedDecl " ++ s ++ "\nType error: " ++ string_of_type_error Σ e
  | AlreadyDeclared s => "Alreadydeclared " ++ s
  end%string.

Definition wrap_EnvCheck {A} (ec : EnvCheck A) : PrettyPrinter A :=
  match ec with
  | CorrectDecl a => ret a
  | EnvError Σ err =>
    printer_fail ("EnvError: " ++ string_of_env_error Σ err)
  end.

Module P := PCUICAst.
Definition wrap_typing_result {A} (Σ : P.global_env) (tr : typing_result A) : PrettyPrinter A :=
  match tr with
  | Checked et => ret et
  | TypeError te =>
    printer_fail ("TypeError: " ++ string_of_type_error (P.empty_ext Σ) te)
  end.

Definition wrap_option {A} (o : option A) (err : string) : PrettyPrinter A :=
  match o with
  | Some a => ret a
  | None => printer_fail err
  end.

Definition wrap_result {T E} (r : result T E) (err_string : E -> string) : PrettyPrinter T :=
  match r with
  | Ok t => ret t
  | Err e => printer_fail (err_string e)
  end.

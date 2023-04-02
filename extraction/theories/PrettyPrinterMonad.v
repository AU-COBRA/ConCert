From Coq Require Import List.
From Coq Require Import Ascii.
From Coq Require Import String.
From MetaCoq.Utils Require Import monad_utils.
From MetaCoq.SafeChecker Require Import PCUICErrors.
From MetaCoq.Erasure.Typed Require Import ResultMonad.
From ConCert.Extraction Require Import Common.

Import monad_utils.MCMonadNotation.
Import ListNotations.
Local Open Scope string.

Import Kernames.

Record PrettyPrinterState :=
  {
    indent_stack : list nat;
    used_names : list ident;
    output_lines : list (nat * string);
    cur_output_line : nat * string;
  }.

Notation bs_to_s := bytestring.String.to_string.
Notation s_to_bs := bytestring.String.of_string.

Local Coercion bs_to_s : bytestring.string >-> string.

Definition PrettyPrinter A :=
  PrettyPrinterState -> result (A * PrettyPrinterState) string.

#[export]
Instance Monad_PrettyPrinter : Monad PrettyPrinter :=
  {| ret _ a pps := Ok (a, pps);
     bind _ _ m f pps :=
       match m pps with
       | Ok (a, pps) => f a pps
       | Err err => Err err
       end |}.

Definition map_pps
           (f : list nat -> list nat)
           (g : list ident -> list ident)
           (h : list (nat * string) -> list (nat * string))
           (i : nat * string -> nat * string) : PrettyPrinter unit :=
  fun pps =>
    Ok (tt,
        let (a, b, c, d) := pps in
        Build_PrettyPrinterState (f a) (g b) (h c) (i d)).

Fixpoint prefix_spaces n s :=
  match n with
  | 0 => s
  | S n => prefix_spaces n (String " "%char s)
  end.

Definition collect_output_lines pps :=
  MCList.rev_map (fun '(n, l) => prefix_spaces n l) (cur_output_line pps :: output_lines pps).

Definition result_string_err A := result A string.

Definition finish_print_lines {A} (pp : PrettyPrinter A) : result_string_err (A * list string) :=
  '(a, pps) <- pp {| indent_stack := [];
                     used_names := [];
                     output_lines := [];
                     cur_output_line := (0, "") |};;
  ret (a, collect_output_lines pps).

Definition collect_output pps :=
  concat nl (collect_output_lines pps).

Definition printer_fail {A} (str : string) : PrettyPrinter A :=
  fun pps => Err (str ++ nl ++ "failed after printing" ++ nl ++ collect_output pps).

Definition finish_print {A} (pp : PrettyPrinter A) : result (A * string) string :=
  '(a, lines) <- finish_print_lines pp;;
  ret (a, concat nl lines).

Definition get_indent : PrettyPrinter nat :=
  fun pps => Ok (hd 0 (indent_stack pps), pps).

Definition map_indent_stack (f : list nat -> list nat) : PrettyPrinter unit :=
  map_pps f id id id.

Definition push_indent (n : nat) : PrettyPrinter unit :=
  map_indent_stack (cons n).

Definition pop_indent : PrettyPrinter unit :=
  map_indent_stack (@tl nat).

Definition get_used_names : PrettyPrinter (list ident) :=
  fun pps => Ok (used_names pps, pps).

Definition map_used_names (f : list ident -> list ident) : PrettyPrinter unit :=
  map_pps id f id id.

Definition push_use (n : ident) : PrettyPrinter unit :=
  map_used_names (cons n).

Definition pop_use : PrettyPrinter unit :=
  map_used_names (@tl _).

Definition get_current_line_length : PrettyPrinter nat :=
  fun pps => Ok ((fst (cur_output_line pps)) + String.length (snd (cur_output_line pps)), pps).

Definition map_cur_output_line (f : nat * string -> nat * string) : PrettyPrinter unit :=
  map_pps id id id f.

Definition append (s : string) : PrettyPrinter unit :=
  map_cur_output_line (fun '(n, prev) => (n, prev ++ s)).

Definition append_nl : PrettyPrinter unit :=
  fun pps =>
    Ok (tt,
        {| indent_stack := indent_stack pps;
           used_names := used_names pps;
           output_lines := cur_output_line pps :: output_lines pps;
           cur_output_line := (hd 0 (indent_stack pps), "") |}).

Definition monad_append_join
           (sep : PrettyPrinter unit)
           (xs : list (PrettyPrinter unit)) : PrettyPrinter unit :=
  monad_fold_left (fun sep' x => sep';; x;; ret sep) xs (ret tt);;
  ret tt.

Definition append_join (sep : string) (s : list string) : PrettyPrinter unit :=
  monad_append_join (append sep) (map append s).

Definition monad_append_concat (xs : list (PrettyPrinter unit)) : PrettyPrinter unit :=
  monad_map id xs;;
  ret tt.

Definition append_concat (xs : list string) : PrettyPrinter unit :=
  monad_append_concat (map append xs).

Definition fresh_name (name : ident) (extra_used : list ident) : PrettyPrinter ident :=
  used <- get_used_names;;
  let used := (extra_used ++ used)%list in
  if existsb (bytestring.String.eqb name) used then
    (fix f n i :=
       match n with
       | 0 => ret (s_to_bs "unreachable")
       | S n =>
         let numbered_name := bytestring.String.append name (MCString.string_of_nat i) in
         if existsb (bytestring.String.eqb numbered_name) used then
           f n (S i)
         else
           ret numbered_name
       end) (S (List.length used)) 2
  else
    ret name.

Definition string_of_env_error Σ e :=
  match e with
  | IllFormedDecl s e =>
    ("IllFormedDecl " ++ s ++ "\nType error: " ++ string_of_type_error Σ e)%string
  | AlreadyDeclared s => "Alreadydeclared " ++ s
  end%string.

Definition wrap_EnvCheck {astr A} f (ec : EnvCheck astr A) : PrettyPrinter A :=
  match ec with
  | CorrectDecl a => ret a
  | EnvError Σ err =>
    printer_fail ("EnvError: " ++ string_of_env_error (f Σ) err)
  end.

Module P := PCUICAst.
Definition wrap_typing_result {A} (Σ : P.PCUICEnvironment.global_env)
                              (tr : typing_result A) : PrettyPrinter A :=
  match tr with
  | Checked et => ret et
  | TypeError te =>
    printer_fail ("TypeError: " ++ string_of_type_error (P.PCUICEnvironment.empty_ext Σ) te)
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

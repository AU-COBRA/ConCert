From ConCert.Execution Require Import Blockchain.
From ConCert.Execution Require Import Serializable.
From ConCert.Execution Require Import Containers.
From ConCert.Extraction Require Import Certified.

From Coq Require Import Ascii.
From Coq Require Import List.
From Coq Require Import String.

From MetaCoq.SafeChecker Require Import PCUICSafeChecker.
From MetaCoq.Template Require Import All.
From MetaCoq.Erasure Require Import Debox Loader SafeTemplateErasure EAst EAstUtils ETyping.

Import ListNotations.
Import MonadNotation.

Local Open Scope string.

Record PrettyPrinterState :=
  {
    indent_stack : list nat;
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

Definition printer_fail {A} (str : string) : PrettyPrinter A :=
  fun pps => inl (str ++ nl ++ "failed after printing" ++ nl ++ (output pps)).

Definition finish_print {A} (pp : PrettyPrinter A) : string + A * string :=
  match pp {| indent_stack := []; output := "" |} with
  | inl err => inl err
  | inr (a, pps) => inr (a, output pps)
  end.

Definition get_indent : PrettyPrinter nat :=
  fun pps => inr (hd 0 (indent_stack pps), pps).

Definition update_indent (f : list nat -> list nat) : PrettyPrinter unit :=
  fun pps => inr (tt, {| indent_stack := f (indent_stack pps); output := output pps |}).

Definition push_indent (n : nat) : PrettyPrinter unit :=
  update_indent (cons n).

Definition pop_indent : PrettyPrinter unit :=
  update_indent tl.

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
  fun pps => inr (last_line_length (output pps), pps).

Definition update_output (f : string -> string) : PrettyPrinter unit :=
  fun pps => inr (tt, {| indent_stack := indent_stack pps; output := f (output pps) |}).

Definition append (s : string) : PrettyPrinter unit :=
  update_output (fun o => o ++ s).

Definition append_nl : PrettyPrinter unit := append nl.

Definition append_indent : PrettyPrinter unit :=
  indent <- get_indent;;
  append (concat "" (repeat " " indent)).

Definition append_nl_and_indent : PrettyPrinter unit :=
  append_nl;; append_indent.

Definition replace_char (orig : Ascii.ascii) (new : Ascii.ascii) : string -> string :=
  fix f s :=
    match s with
    | EmptyString => EmptyString
    | String c s => if (c =? orig)%char then
                      String new (f s)
                    else
                      String c (f s)
    end.

Definition printable_kername : kername -> string :=
  replace_char "." "_".

Local Open Scope list.

Section PrintMidlang.

Context (Σ : global_context).
Context (indent_size := 2).

Definition lookup_ind_decl ind i : PrettyPrinter one_inductive_body :=
  match lookup_env Σ ind with
  | Some (InductiveDecl {| ind_bodies := l |}) =>
    match nth_error l i with
    | Some body => ret body
    | None => printer_fail ("could not find inductive " ++ string_of_nat i ++ " in inductive " ++ ind)
    end
  | _ => printer_fail ("could not find " ++ ind ++ " in environment")
  end.

Definition print_name (n : name) : PrettyPrinter unit :=
  match n with
  | nAnon => append "_"
  | nNamed n => append n
  end.

Definition print_constructor_name (ind : inductive) (i : nat) : PrettyPrinter unit :=
  oib <- lookup_ind_decl (inductive_mind ind) (inductive_ind ind);;
  match nth_error (ind_ctors oib) i with
  | Some (name, _, _) =>
    append name
    (*append (replace_char "." "_" (inductive_mind ind) ++ "_" ++ name)*)
  | None =>
    printer_fail (inductive_mind ind ++ " does not have a ctor " ++ string_of_nat i)
  end.

Definition print_parenthesized
           (parenthesize : bool)
           (print : PrettyPrinter unit) : PrettyPrinter unit :=
  if parenthesize then
    append "(";; print;; append ")"
  else
    print.

Definition parenthesize_app_head (t : term) : bool :=
  match t with
  | tLambda _ _
  | tLetIn _ _ _
  | tCase _ _ _
  | tFix _ _ => true
  | _ => false
  end.

Definition parenthesize_app_arg (t : term) : bool :=
  match t with
  | tLambda _ _
  | tLetIn _ _ _
  | tApp _ _
  | tCase _ _ _
  | tProj _ _
  | tFix _ _ => true
  | _ => false
  end.

Definition parenthesize_case_discriminee (t : term) : bool :=
  match t with
  | tLetIn _ _ _
  | tCase _ _ _ => true
  | _ => false
  end.

Definition parenthesize_case_branch (t : term) : bool :=
  false.

Definition add_name (name : name) (Γ : list ident) : list ident :=
  let name :=
      match name with
      | nAnon => "anon" (* fix *)
      | nNamed name => name
      end in
  name :: Γ.

Fixpoint print_term (Γ : list ident) (t : term) {struct t} : PrettyPrinter unit :=
  match t with
  | tBox _ => printer_fail "tBox"
  | tRel n =>
    match nth_error Γ n with
    | Some name => append name
    | None => printer_fail ("unbound tRel " ++ string_of_nat n)
    end
  | tVar ident => printer_fail ("tVar " ++ ident)
  | tEvar _ _ => printer_fail "unexpected evar"
  | tLambda name t =>
    append "\";;
    print_name name;;
    append " -> ";;
    print_term (add_name name Γ) t

  | tLetIn name value body =>

    let_col <- get_current_line_length;;
    append "let";;

    push_indent (let_col + indent_size);;

    let print_and_add_one Γ name value :=
        append_nl_and_indent;;

        print_name name;;
        append " =";;

        indent <- get_indent;;
        push_indent (indent + indent_size);;
        append_nl_and_indent;;

        print_term Γ value;;

        pop_indent;;

        ret (add_name name Γ) in

    Γ <- print_and_add_one Γ name value;;

    (* Print in Midlang/Elm style, which collapses multiple lets into one *)
    (fix print_lets Γ (t : term) :=
       match t with
       | tLetIn name value t =>
         Γ <- print_and_add_one Γ name value;;
         print_lets Γ t
       | _ =>
         pop_indent;; (* indent in let block *)

         append_nl_and_indent;; (* indent to 'let' keyword *)
         append "in";;

         append_nl_and_indent;; (* body is indented to 'let'/'in' keyword as well *)
         print_term Γ t;;
         pop_indent
       end) Γ body

  | tApp head arg =>
    print_parenthesized (parenthesize_app_head head) (print_term Γ head);;
    append " ";;
    print_parenthesized (parenthesize_app_arg arg) (print_term Γ arg)

  | tConst name => append (printable_kername name)
  | tConstruct ind i => print_constructor_name ind i

  | tCase (ind, _) discriminee branches =>
    case_col <- get_current_line_length;;
    append "case ";;
    print_parenthesized (parenthesize_case_discriminee discriminee)
                        (print_term Γ discriminee);;
    append " of";;

    push_indent (case_col + indent_size);;

    oib <- lookup_ind_decl (inductive_mind ind) (inductive_ind ind);;

    (* Take care that this is structurally recursive... *)
    (fix print_branches (branches : list (nat * term)) (ctor_names : list ident) :=
       match branches, ctor_names with
       | [], [] => ret tt
       | (arity, t) :: branches, ctor_name :: ctor_names =>
         append_nl_and_indent;;

         ctor_indent <- get_indent;;
         push_indent (ctor_indent + indent_size);;

         append ctor_name;;

         (fix print_branch (n : nat) (Γ : list ident) (t : term) {struct t} :=
            match n with
            | 0 =>
              append " ->";;
              append_nl_and_indent;;
              print_parenthesized (parenthesize_case_branch t) (print_term Γ t)

            | S n =>
              match t with
              | tLambda name t =>
                append " ";;
                print_name name;;
                print_branch n (add_name name Γ) t

              | _ => printer_fail "could not decompose branch"
              end
            end) arity Γ t;;

         pop_indent;;

         print_branches branches ctor_names
       | _, _ => printer_fail "wrong number of case branches compared to inductive"
       end) branches (map (fun '(name, _, _) => name) (ind_ctors oib));;

    pop_indent

  | tProj _ _ => printer_fail "tProj"
  | tFix _ _ => printer_fail "tFix"
  | tCoFix _ _ => printer_fail "Cannot handle cofix"
  end.

(*
Fixpoint print_global_declarations (l : list (kername * global_decl)) : PrettyPrinter unit :=
  match l with
  | (name, decl) :: l =>
    match decl with
    | ConstantDecl
*)

End PrintMidlang.

Local Open Scope nat.

Inductive Msg :=
| increment
| decrement.

(*
Quote Recursively Definition test :=
  (fun (state : nat) (maybe_msg : option Msg) =>
    match maybe_msg with
    | Some increment => Some (state + 1)
    | Some decrement => Some (state - 1)
    | _ => None
    end).
*)

Quote Recursively Definition test :=
  (let x := 5 in
  let foo n := S n in
  let y := 7 in
  x + foo 3 + y + foo (foo x)).

Compute erase_check_debox_all_print [] "foo" [] test.

Definition test2 : string :=
  match erase_check_debox_all [] test with
  | CorrectDecl (Σ, (args, term)) =>
    match finish_print (append_nl;; print_term Σ ["f"] term) with
    | inl err => "Printer error: " ++ err
    | inr (_, output) => output
    end
  | EnvError Σ (AlreadyDeclared id) => "Already declared: " ++ id
  | EnvError Σ (IllFormedDecl id e) =>
    "Type error: " ++ PCUICSafeChecker.string_of_type_error Σ e ++ ", while checking " ++ id
  end.

Compute test2.

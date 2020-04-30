From ConCert.Execution Require Import Blockchain.
From ConCert.Execution Require Import Serializable.
From ConCert.Execution Require Import Containers.
From ConCert.Extraction Require Import Certified.

From Coq Require Import Arith.
From Coq Require Import Ascii.
From Coq Require Import List.
From Coq Require Import String.

From MetaCoq.SafeChecker Require Import PCUICSafeChecker SafeTemplateChecker.
From MetaCoq.Template Require Import All.
From MetaCoq.Erasure Require Import Debox Loader SafeTemplateErasure EAst EAstUtils ETyping.

Module P := MetaCoq.PCUIC.PCUICAst.
Module PT := MetaCoq.PCUIC.PCUICTyping.
Module T2P := MetaCoq.PCUIC.TemplateToPCUIC.
Module E := MetaCoq.Erasure.EAst.
Module T := MetaCoq.Template.Ast.
Module EF := MetaCoq.Erasure.SafeErasureFunction.

Import ListNotations.
Import MonadNotation.

Local Open Scope string.

Module Ex.
  Record constant_body :=
    { cst_type : P.term;
      cst_body : option E.term; }.

  Inductive global_decl :=
  | ConstantDecl : constant_body -> global_decl
  | InductiveDecl : P.mutual_inductive_body -> global_decl.

  Definition global_env := list (kername * global_decl).

  Fixpoint lookup_env (Σ : global_env) (id : ident) : option global_decl :=
    match Σ with
    | [] => None
    | (name, decl) :: Σ => if ident_eq id name then Some decl else lookup_env Σ id
    end.
End Ex.

Record PrettyPrinterState :=
  {
    indent_stack : list nat;
    used_names : list ident;
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
  match pp {| indent_stack := [];
              used_names := [];
              output := "" |} with
  | inl err => inl err
  | inr (a, pps) => inr (a, output pps)
  end.

Definition get_indent : PrettyPrinter nat :=
  fun pps => inr (hd 0 (indent_stack pps), pps).

Definition update_indent (f : list nat -> list nat) : PrettyPrinter unit :=
  fun pps => inr (tt, {| indent_stack := f (indent_stack pps);
                         used_names := used_names pps;
                         output := output pps |}).

Definition push_indent (n : nat) : PrettyPrinter unit :=
  update_indent (cons n).

Definition pop_indent : PrettyPrinter unit :=
  update_indent tl.

Definition get_used_names : PrettyPrinter (list ident) :=
  fun pps => inr (used_names pps, pps).

Definition update_used_names (f : list ident -> list ident) : PrettyPrinter unit :=
  fun pps => inr (tt, {| indent_stack := indent_stack pps;
                         used_names := f (used_names pps);
                         output := output pps |}).

Definition push_use (n : ident) : PrettyPrinter unit :=
  update_used_names (cons n).

Definition pop_use : PrettyPrinter unit :=
  update_used_names tl.

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
  fun pps => inr (tt, {| indent_stack := indent_stack pps;
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

Definition replace_char (orig : Ascii.ascii) (new : Ascii.ascii) : string -> string :=
  fix f s :=
    match s with
    | EmptyString => EmptyString
    | String c s => if (c =? orig)%char then
                      String new (f s)
                    else
                      String c (f s)
    end.

Definition last_index_of (c : ascii) (s : string) : option nat :=
  (fix f (s : string) (index : nat) (result : option nat) :=
     match s with
     | EmptyString => result
     | String c' s =>
       if (c' =? c)%char then
         f s (S index) (Some index)
       else
         f s (S index) result
     end) s 0 None.

Definition to_upper (c : ascii) : ascii :=
  match c with
  | Ascii b0 b1 b2 b3 b4 b5 b6 b7 =>
    Ascii b0 b1 b2 b3 b4 false b6 b7
  end.

Definition capitalize (s : string) : string :=
  match s with
  | EmptyString => EmptyString
  | String c s => String (to_upper c) s
  end.

Definition printable_kername (name : kername) : string :=
  match last_index_of "." name with
  | Some n => substring (S n) (length name) name
  | None => name
  end.

Definition kername_qualifier (name : kername) : string :=
  match last_index_of "." name with
  | Some n => substring 0 n name
  | None => ""
  end.

Local Open Scope list.

Local Definition indent_size := 2.

Section FixExEnv.

Context (Σ : Ex.global_env).

Definition print_ty_name (name : kername) : PrettyPrinter unit :=
  append (capitalize (printable_kername name)).

Definition print_ctor_name (name : ident) : PrettyPrinter unit :=
  append (capitalize name).

Definition lookup_mind (name : kername) : option P.mutual_inductive_body :=
  match Ex.lookup_env Σ name with
  | Some (Ex.InductiveDecl mind) => Some mind
  | _ => None
  end.

Definition lookup_ind_decl (ind : inductive) : PrettyPrinter P.one_inductive_body :=
  match lookup_mind (inductive_mind ind) with
  | Some {| P.ind_bodies := l |} =>
    match nth_error l (inductive_ind ind) with
    | Some body => ret body
    | None => printer_fail ("could not find inductive " ++
                            string_of_nat (inductive_ind ind) ++
                            " in inductive " ++ inductive_mind ind)
    end
  | _ => printer_fail ("could not find " ++ inductive_mind ind ++ " in environment")
  end.

Definition print_ind_ctor (ind : inductive) (i : nat) : PrettyPrinter unit :=
  oib <- lookup_ind_decl ind;;
  match nth_error (P.ind_ctors oib) i with
  | Some (name, _, _) =>
    print_ctor_name name
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

Definition fresh (name : ident) (used : list ident) : ident :=
  if existsb (String.eqb name) used then
    (fix f n i :=
       match n with
       | 0 => "unreachable"
       | S n =>
         let numbered_name := (name ++ string_of_nat i)%string in
         if existsb (String.eqb numbered_name) used then
           f n (S i)
         else
           numbered_name
       end) (S (List.length used)) 2
  else
    name.

Definition fresh_name (name : name) (Γ : list ident) : PrettyPrinter ident :=
  used_names <- get_used_names;;
  match name with
  | nAnon => ret (fresh "_x" (Γ ++ used_names))
  | nNamed name => ret (fresh name (Γ ++ used_names))
  end.

(*
Definition blah :=
  fix f x :=
    match x with
    | S x => (g x + f x)%nat
    | 0 => 0
    end
 with g x :=
      match x with
      | S x => (g x + f x)%nat
      | 0 => 0
      end
for f.

Quote Recursively Definition foo := blah.
*)

Import P.
Definition parenthesize_prod_domain (t : term) : bool :=
  match t with
  | tProd _ _ _ => true
  | _ => false
  end.

Fixpoint print_type (t : term) : PrettyPrinter unit :=
  match t with
  | tInd ind _ => print_ty_name (inductive_mind ind)
  | tProd _ dom cod =>
    print_parenthesized (parenthesize_prod_domain dom) (print_type dom);;
    append " -> ";;
    print_type cod
  | _ => printer_fail ("cannot print following as type" ++ nl ++ PCUICAstUtils.string_of_term t)
  end.

Import E.
(* Print something of the form
   foo =
     a b c
inlining lambdas (and fix points). For example, for
   foo = \x \y \z -> z
instead print
   foo x y z = z
*)
Definition print_define_term
         (Γ : list ident)
         (name : ident)
         (t : term)
         (print_term : list ident -> term -> PrettyPrinter unit) : PrettyPrinter unit :=
  name_col <- get_current_line_length;;
  append name;;

  let fix print_decompose Γ t :=
      match t with
      | tLambda arg_name t =>
        arg_name <- fresh_name arg_name Γ;;
        append (" " ++ arg_name);;
        print_decompose (arg_name :: Γ) t
      | _ =>
        append " =";;
        push_indent (name_col + indent_size);;
        append_nl_and_indent;;
        print_term Γ t;;
        pop_indent
      end in

  match t with
  | tFix [d] 0 => print_decompose (name :: Γ) (dbody d)
  | _ => print_decompose Γ t
  end.

Fixpoint print_term (Γ : list ident) (t : term) : PrettyPrinter unit :=
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

    name <- fresh_name name Γ;;
    append name;;
    append " -> ";;
    print_term (name :: Γ) t

  | tLetIn name value body =>

    let_col <- get_current_line_length;;
    push_indent let_col;;

    append "let";;

    let print_and_add_one Γ name value :=
        append_nl_and_indent;;
        name <- fresh_name name Γ;;
        (* We will define this name to make sure we don't reuse it
           until the let is all over. Midlang does not allow shadowing. *)
        push_use name;;
        print_define_term Γ name value print_term;;
        ret (name :: Γ) in

    push_indent (let_col + indent_size);;

    Γ <- print_and_add_one Γ name value;;

    (* Print in Midlang/Elm style, which collapses multiple lets into one *)
    (* Turned off because of Elm's insane shadowing rules *)
    (*
    num_collapsed <-
    (fix print_lets Γ (t : term) :=
       match t with
       | tLetIn name value t =>
         Γ <- print_and_add_one Γ name value;;
         n <- print_lets Γ t;;
         ret (S n)
       | _ =>
         pop_indent;; (* indent in let block *)

         append_nl_and_indent;; (* indent to 'let' keyword *)
         append "in";;

         append_nl_and_indent;; (* body is indented to 'let'/'in' keyword as well *)
         print_term Γ t;;
         pop_indent;;
         ret 0
       end) Γ body;;

    (* pop all the names we defined, we can reuse those names now. *)
    monad_fold_left (fun _ _ => pop_use) (repeat tt (S num_collapsed)) tt
    *)

    pop_indent;;
    append_nl_and_indent;;

    append "in";;
    append_nl_and_indent;;
    print_term Γ body;;
    pop_indent;;

    pop_use

  | tApp head arg =>
    print_parenthesized (parenthesize_app_head head) (print_term Γ head);;
    append " ";;
    print_parenthesized (parenthesize_app_arg arg) (print_term Γ arg)

  | tConst name => append (printable_kername name)
  | tConstruct ind i => print_ind_ctor ind i

  | tCase (ind, _) discriminee branches =>
    case_col <- get_current_line_length;;
    append "case ";;
    print_parenthesized (parenthesize_case_discriminee discriminee)
                        (print_term Γ discriminee);;
    append " of";;

    push_indent (case_col + indent_size);;

    oib <- lookup_ind_decl ind;;

    (* Take care that this is structurally recursive... *)
    (fix print_branches (branches : list (nat * term)) (ctor_names : list ident) :=
       match branches, ctor_names with
       | [], [] => ret tt
       | (arity, t) :: branches, ctor_name :: ctor_names =>
         append_nl_and_indent;;

         ctor_indent <- get_indent;;
         push_indent (ctor_indent + indent_size);;

         print_ctor_name ctor_name;;

         (fix print_branch (n : nat) (Γ : list ident) (t : term) {struct t} :=
            match n with
            | 0 =>
              append " ->";;
              append_nl_and_indent;;
              print_parenthesized (parenthesize_case_branch t) (print_term Γ t)

            | S n =>
              match t with
              | tLambda name t =>
                name <- fresh_name name Γ;;
                append (" " ++ name);;
                print_branch n (name :: Γ) t

              | _ => printer_fail "could not decompose branch"
              end
            end) arity Γ t;;

         pop_indent;;

         print_branches branches ctor_names
       | _, _ => printer_fail "wrong number of case branches compared to inductive"
       end) branches (map (fun '(name, _, _) => name) (P.ind_ctors oib));;

    pop_indent

  | tProj _ _ => printer_fail "tProj"

  | tFix mfix nfix =>
    let_col <- get_current_line_length;;
    push_indent let_col;;

    (* Add names of fixes to context *)
    Γ <- monad_fold_left
           (fun Γ d => name <- fresh_name (dname d) Γ;;
                       ret (name :: Γ)) mfix Γ;;
    let names := rev (firstn (List.length mfix) Γ) in

    append "let";;

    push_indent (let_col + indent_size);;

    (fix print_fixes (ds : list (def term)) (names : list ident) :=
       match ds, names with
       | [], _ => ret tt
       | d :: ds, name :: names =>
         append_nl_and_indent;;
         print_define_term Γ name (dbody d) print_term;;
         print_fixes ds names
       | _, _ =>
         printer_fail "unreachable"
       end) mfix names;;

    pop_indent;;

    append_nl_and_indent;;
    append "in";;
    append_nl_and_indent;;
    match nth_error names nfix with
    | Some n => append n
    | None => printer_fail "invalid fix index"
    end;;

    pop_indent

  | tCoFix _ _ => printer_fail "Cannot handle cofix"
  end.

Definition print_constant_body (name : kername) (cst : Ex.constant_body) : PrettyPrinter unit :=
  name_col <- get_current_line_length;;

  push_indent name_col;;

  let (type, body) := cst in

  append (printable_kername name);;
  append " : ";;
  print_type type;;

  match body with
  | None => ret tt
  | Some body =>
    append_nl_and_indent;;
    let name := printable_kername name in
    push_use name;;
    print_define_term [] name body print_term
  end;;

  pop_indent.

Quote Recursively Definition foo := (5+5)%nat.

Fixpoint decompose_ind_ctor (arity : nat) (ty : P.term) : PrettyPrinter (list P.term) :=
  match arity with
  | 0 => ret []
  | S arity =>
    match ty with
    | P.tProd _ dom cod =>
      tl <- decompose_ind_ctor arity cod;;
      ret (dom :: tl)
    | _ =>
      printer_fail ("unexpected type of ctor: " ++ PCUICAstUtils.string_of_term ty)
    end
  end.

Import P.
Definition parenthesize_ind_ctor_ty (ty : term) : bool :=
  match ty with
  | tInd _ _
  | tVar _ => false
  | _ => true
  end.

Definition print_ind_ctor_definition
           (ind_name : string)
           (name : ident)
           (ty : P.term)
           (arity : nat) : PrettyPrinter unit :=
  print_ctor_name name;;
  tys <- decompose_ind_ctor arity ty;;

  (fix f (tys : list P.term) (depth : nat) :=
     match tys with
     | [] => ret tt
     | ty :: tys =>
       append " ";;
       match ty with
       | tRel n =>
         if (n =? depth)%nat then
           print_ty_name ind_name
          else
            printer_fail ("cannot handle " ++ PCUICAstUtils.string_of_term ty ++ " in inductive")
       | _ => print_parenthesized (parenthesize_ind_ctor_ty ty) (print_type ty)
       end;;
       f tys (S depth)
     end) tys 0.

Local Open Scope string.
Definition print_mutual_inductive_body
           (name : kername)
           (mib : P.mutual_inductive_body) : PrettyPrinter unit :=
  col <- get_current_line_length;;
  push_indent col;;

  let qualifier := kername_qualifier name in

  (fix print_ind_bodies (l : list P.one_inductive_body) (first : bool) :=
     match l with
     | [] => ret tt
     | oib :: l =>

       (if first then ret tt else append_nl_and_indent);;

       append "type ";;
       let ind_name := qualifier ++ "." ++ P.ind_name oib in
       print_ty_name ind_name;;

       push_indent (col + indent_size);;

       (fix print_ind_ctors (ctors : list (ident * P.term * nat)) prefix :=
          match ctors with
          | [] => ret tt
          | (name, ty, arity) :: ctors =>
            append_nl_and_indent;;
            append (prefix ++ " ");;
            print_ind_ctor_definition ind_name name ty arity;;

            print_ind_ctors ctors "|"
          end) (ind_ctors oib) "=";;

       pop_indent;;

       print_ind_bodies l false
     end) (ind_bodies mib) true;;

  pop_indent.

Definition print_global_decl
           (name : kername)
           (decl : Ex.global_decl) : PrettyPrinter unit :=
  match decl with
  | Ex.ConstantDecl cst => print_constant_body name cst
  | Ex.InductiveDecl mib => print_mutual_inductive_body name mib
  end.

Definition print_env : PrettyPrinter unit :=
  sig_col <- get_current_line_length;;
  push_indent sig_col;;

  (fix f (l : Ex.global_env) (first : bool) :=
     match l with
     | (name, decl) :: l =>

       (if first then ret tt else (append_nl;; append_nl_and_indent));;
       print_global_decl name decl;;

       f l false
     | [] => ret tt
     end) Σ true;;

  pop_indent.
End FixExEnv.

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

Definition wrap_typing_result {A} (Σ : P.global_env) (tr : typing_result A) : PrettyPrinter A :=
  match tr with
  | Checked et => ret et
  | TypeError te =>
    printer_fail ("TypeError: " ++ string_of_type_error (P.empty_ext Σ) te)
  end.

Axiom assump : string -> forall {A}, A.

Lemma wf_empty_ext (Σ : P.global_env) :
  ∥PT.wf Σ∥ -> ∥PT.wf_ext (P.empty_ext Σ)∥.
Proof.
  intros [wfΣ].
  constructor.
  split; [assumption|].
  todo "on_udecl on empty_ext".
Qed.

Lemma proj_wf
      {Σ : P.global_env_ext}
      (wfΣ : ∥PT.wf_ext Σ∥) : ∥PT.wf Σ.1∥.
Proof. firstorder. Qed.

Definition erase_and_debox_single
           (Σ : P.global_env_ext)
           (wfΣ : ∥PT.wf_ext Σ∥)
           (decl : P.global_decl) : PrettyPrinter Ex.global_decl :=
  match decl with
  | P.ConstantDecl cst =>
    let (type, body, _) := cst in
    ebody <- match body with
             | None => ret None
             | Some body =>
               ebody <- wrap_typing_result
                          Σ.1
                          (EF.erase Σ wfΣ [] body (assump "assuming well-typedness"));;
               result <- wrap_EnvCheck (check_applied Σ.1 ebody (proj_wf wfΣ));;
               if result then
                 ret (Some (debox_all ebody))
               else
                 printer_fail "Not all constructors or constants are appropriately applied"
             end;;
    ret (Ex.ConstantDecl {| Ex.cst_type := type; Ex.cst_body := ebody |})
  | P.InductiveDecl mib =>
    (*mib <- wrap_typing_result
             Σ.1
             (EF.erase_mutual_inductive_body Σ wfΣ mib);;*)
    ret (Ex.InductiveDecl mib)
  end.

(* Extract the specified environment to Midlang, creating definitions for all symbols. *)
Definition extract_env (Σ : T.global_env) : PrettyPrinter unit :=
  let Σ := fix_global_env_universes Σ in
  let Σ := (T2P.trans_global (T.empty_ext Σ)).1 in
  G <- wrap_EnvCheck (check_wf_env_only_univs Σ);;
  let wfΣ := G.π2.p2 in
  let Σext := P.empty_ext Σ in
  let wfΣext : ∥PT.wf_ext Σext∥ := wf_empty_ext Σ wfΣ in
  Σex <- monad_map (fun '(name, decl) =>
                      decl <- erase_and_debox_single Σext wfΣext decl;;
                      ret (name, decl)) Σ;;
  print_env Σex.

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

Definition app (f : nat -> nat) (n : nat) : nat :=
  f n.

Definition test : nat :=
  let x := 5 in
  let foo n := S n in
  let even :=
      fix even n :=
        match n with
        | 0 => true
        | S n => odd n
        end
     with odd n :=
        match n with
        | 0 => false
        | S n => even n
        end
      for even in
  let fix even n :=
      match n with
      | 0 => true
      | 1 => false
      | S (S n) => even n
      end in
  let y := 7 in
  x + app (fun x => S x) (foo 3) + y + foo (foo x) + if even x then 2 else 0.

Definition test' : bool :=
  let x := let y := true in y in
  let y := x in y.

Quote Recursively Definition test_program := test.

Local Open Scope string.
Definition test3 :=
  match finish_print (append_nl;; extract_env test_program.1) with
  | inl err => "Printer error: " ++ err
  | inr (_, output) => output
  end.

Compute test3.

Compute erase_check_debox_all_print [] "foo" [] test_program.

Definition test2 : string :=
  match erase_check_debox_all [] test_program with
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

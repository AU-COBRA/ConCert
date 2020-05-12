From ConCert.Execution Require Import Blockchain.
From ConCert.Execution Require Import Serializable.
From ConCert.Execution Require Import Containers.
From ConCert.Extraction Require Import Certified.
From ConCert.Extraction Require Import Common.
From ConCert.Extraction Require Import PrettyPrinterMonad.
From ConCert.Extraction Require Import ResultMonad.
From ConCert.Extraction Require Import StringExtra.

From Coq Require Import Arith.
From Coq Require Import Ascii.
From Coq Require Import List.
From Coq Require Import NArith.
From Coq Require Import PArith.
From Coq Require Import String.

From MetaCoq.SafeChecker Require Import PCUICSafeChecker SafeTemplateChecker.
From MetaCoq.Template Require Import All.
From MetaCoq.Erasure Require Import Debox Loader SafeTemplateErasure EAst EAstUtils ETyping.

Module P := MetaCoq.PCUIC.PCUICAst.
Module PT := MetaCoq.PCUIC.PCUICTyping.
Module T2P := MetaCoq.PCUIC.TemplateToPCUIC.
Module E := MetaCoq.Erasure.EAst.
Module T := MetaCoq.Template.Ast.
Module TUtil := MetaCoq.Template.AstUtils.
Module EF := MetaCoq.Erasure.SafeErasureFunction.
Module Ex := Common.

Import PrettyPrinterMonad.
Import ListNotations.
Import MonadNotation.

Local Open Scope list.
Local Open Scope string.

Local Definition indent_size := 2.

Section FixExEnv.
Context (Σ : Ex.global_env).

Bind Scope string with kername ident.

Definition get_fun_name (name : kername) : string :=
  uncapitalize (replace_char "." "_" name).

Definition get_ty_name (name : kername) : string :=
  capitalize (replace_char "." "_" name).

Definition get_ctor_name (name : ident) : string :=
  capitalize name.

Definition get_ty_arg_name (name : ident) : ident :=
  uncapitalize name.

Definition lookup_mind (name : kername) : option Ex.mutual_inductive_body :=
  match Ex.lookup_env Σ name with
  | Some (Ex.InductiveDecl mib) => Some mib
  | _ => None
  end.

Definition lookup_ind_decl (ind : inductive) : PrettyPrinter Ex.one_inductive_body :=
  match lookup_mind (inductive_mind ind) with
  | Some {| Ex.ind_bodies := l |} =>
    match nth_error l (inductive_ind ind) with
    | Some body => ret body
    | None => printer_fail ("could not find inductive " ++
                            string_of_nat (inductive_ind ind) ++
                            " in inductive " ++ inductive_mind ind)
    end
  | _ => printer_fail ("could not find " ++ inductive_mind ind ++ " in environment")
  end.

Definition print_ind (ind : inductive) : PrettyPrinter unit :=
  oib <- lookup_ind_decl ind;;
  let qual := kername_qualifier (inductive_mind ind) in
  append (get_ty_name (qual ++ "." ++ Ex.ind_name oib)).

Definition print_ind_ctor (ind : inductive) (i : nat) : PrettyPrinter unit :=
  oib <- lookup_ind_decl ind;;
  match nth_error (Ex.ind_ctors oib) i with
  | Some (name, _) =>
    append (get_ctor_name name)
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
         let numbered_name := name ++ string_of_nat i in
         if existsb (String.eqb numbered_name) used then
           f n (S i)
         else
           numbered_name
       end) (S (List.length used)) 2
  else
    name.

Definition fresh_ident (name : name) (Γ : list ident) : PrettyPrinter ident :=
  used_names <- get_used_names;;
  match name with
  | nAnon => ret (fresh "_x" (Γ ++ used_names))
  | nNamed name => ret (fresh (remove_char "'" name) (Γ ++ used_names))
  end.

Definition fresh_ty_arg_name (name : name) (Γ : list ident) : PrettyPrinter ident :=
  used_names <- get_used_names;;
  match name with
  | nAnon => ret (fresh "a" (Γ ++ used_names))
  | nNamed name => ret (fresh (get_ty_arg_name name) (Γ ++ used_names))
  end.

Import P.
Definition parenthesize_prod_domain (t : box_type) : bool :=
  match t with
  | TArr _ _ => true
  | _ => false
  end.

Definition parenthesize_ty_app_arg (t : box_type) : bool :=
  match t with
  | TApp _ _ => true
  | _ => false
  end.

Fixpoint print_type (Γ : list ident) (t : box_type) : PrettyPrinter unit :=
  match t with
  | TBox _ => printer_fail "unexpected box in type"
  | TArr dom cod =>
    print_parenthesized
      (parenthesize_prod_domain dom)
      (print_type Γ dom);;
    append " -> ";;
    print_type Γ cod
  | TApp head arg =>
    print_type Γ head;;
    append " ";;
    print_parenthesized (parenthesize_ty_app_arg arg) (print_type Γ arg)
  | TRel n =>
    match nth_error Γ n with
    | Some name => append name
    | None => printer_fail ("unbound TRel " ++ string_of_nat n)
    end
  | TInd ind => print_ind ind
  | TConst _ => printer_fail "Cannot handle type aliases"
  end.

Import E.
(* Print something of the form
   foo =
     a b c
inlining lambdas and fix points. For example, for
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
        arg_name <- fresh_ident arg_name Γ;;
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

    name <- fresh_ident name Γ;;
    append name;;
    append " -> ";;
    print_term (name :: Γ) t

  | tLetIn name value body =>

    let_col <- get_current_line_length;;
    push_indent let_col;;

    append "let";;

    let print_and_add_one Γ name value :=
        append_nl_and_indent;;
        name <- fresh_ident name Γ;;
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

  | tConst name => append (get_fun_name name)
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

         append (get_ctor_name ctor_name);;

         (fix print_branch (n : nat) (Γ : list ident) (t : term) {struct t} :=
            match n with
            | 0 =>
              append " ->";;
              append_nl_and_indent;;
              print_parenthesized (parenthesize_case_branch t) (print_term Γ t)

            | S n =>
              match t with
              | tLambda name t =>
                name <- fresh_ident name Γ;;
                append (" " ++ name);;
                print_branch n (name :: Γ) t

              | _ => printer_fail "could not decompose branch"
              end
            end) arity Γ t;;

         pop_indent;;

         print_branches branches ctor_names
       | _, _ => printer_fail "wrong number of case branches compared to inductive"
       end) branches (map fst (Ex.ind_ctors oib));;

    pop_indent

  | tProj _ _ => printer_fail "tProj"

  | tFix mfix nfix =>
    let_col <- get_current_line_length;;
    push_indent let_col;;

    (* Add names of fixes to context *)
    Γ <- monad_fold_left
           (fun Γ d => name <- fresh_ident (dname d) Γ;;
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

Definition print_constant_body
           (name : kername)
           (cst : Ex.constant_body) : PrettyPrinter string :=
  name_col <- get_current_line_length;;

  push_indent name_col;;

  let (type, body) := cst in

  let ml_name := get_fun_name name in
  (*
  append ml_name;;
  append " : ";;
  print_type [] type;;*)

  match body with
  | None => ret tt
  | Some body =>
    let name := get_fun_name name in
    push_use name;;
    print_define_term [] name body print_term
  end;;

  pop_indent;;

  ret ml_name.

Definition decompose_ind_ctor
         (nparams : nat)
         (arity : nat)
         (t : P.term) : PrettyPrinter (list P.term) :=
  (* First get rid of parameters. The constructor will always start with those *)
  t <- (fix f n t :=
           match n, t with
           | 0, _ => ret t
           | S n, tProd _ (tSort _) t => f n t
           | _, _ => printer_fail ("unexpected type of ctor: " ++ PCUICAstUtils.string_of_term t)
           end) nparams t;;

  (fix f n t :=
     match n with
     | 0 => ret []
     | S n =>
       match t with
       | P.tProd _ dom cod =>
         tl <- f n cod;;
         ret (dom :: tl)
       | _ =>
         printer_fail ("unexpected type of ctor: " ++ PCUICAstUtils.string_of_term t)
       end
     end) arity t.

Import P.
Definition parenthesize_ind_ctor_ty (ty : box_type) : bool :=
  match ty with
  | TRel _
  | TInd _
  | TConst _ => false
  | _ => true
  end.

Definition print_ind_ctor_definition
           (Γ : list ident)
           (name : ident)
           (data : list box_type) : PrettyPrinter unit :=
  append (get_ctor_name name);;

  monad_fold_left (fun _ bty =>
                     append " ";;
                     print_parenthesized
                       (parenthesize_ind_ctor_ty bty)
                       (print_type Γ bty)) data tt.

Local Open Scope string.
Import Ex.
Definition print_mutual_inductive_body
           (name : kername)
           (mib : mutual_inductive_body) : PrettyPrinter (list (kername * string)) :=
  col <- get_current_line_length;;
  push_indent col;;

  let qualifier := kername_qualifier name in

  (* make context that has mutual inductive bodies *)
  let Γ := map (fun oib => get_ty_name (qualifier ++ "." ++ ind_name oib))
               (ind_bodies mib) in

  (*
  Γ <- monad_fold_left
         (fun Γ name =>
            name <- fresh_ty_arg_name name;;
            ret (name :: Γ)) (Ex.ind_type_parameters
  (* add parameters *)
  Γ <- monad_fold_left
         (fun Γ d =>
            match decl_body d with
            | None => ret tt
            | Some _ => printer_fail "cannot handle inductive parameter with body"
            end;;
            match decl_type d with
            | tSort _ => ret tt
            | t => printer_fail "can only handle parameters of type sort"
            end;;
            name <- fresh_ty_arg_name (decl_name d) Γ;;
            ret (name :: Γ)) (rev (ind_params mib)) Γ;;

  let ty_arg_names := rev (firstn (List.length (ind_params mib)) Γ) in
*)

  names <-
  (fix print_ind_bodies
       (l : list one_inductive_body)
       (first : bool)
       (names : list (kername * string)) :=
     match l with
     | [] => ret names
     | oib :: l =>

       (if first then ret tt else append_nl_and_indent);;

       (* Add type parameters. Note that since we are in prenex form,
          our context will have last type parameter last, not first. *)
       let length_before := List.length Γ in
       Γ <- monad_fold_left
              (fun Γ name =>
                 name <- fresh_ty_arg_name name Γ;;
                 ret (Γ ++ [name])%list) (ind_type_parameters oib) Γ;;

       (* Get the fresh names we generated from the context *)
       let ty_arg_names := skipn length_before Γ in

       append "type ";;
       let ind_name := qualifier ++ "." ++ ind_name oib in
       let ind_ml_name := get_ty_name ind_name in
       append ind_ml_name;;

       (* Print type args *)
       monad_fold_left (fun _ name => append (" " ++ name)) ty_arg_names tt;;

       push_indent (col + indent_size);;

       (fix print_ind_ctors (ctors : list (ident * list D.box_type)) prefix :=
          match ctors with
          | [] => ret tt
          | (name, data) :: ctors =>
            append_nl_and_indent;;
            append (prefix ++ " ");;
            print_ind_ctor_definition Γ name data;;

            print_ind_ctors ctors "|"
          end) (ind_ctors oib) "=";;

       pop_indent;;

       print_ind_bodies l false ((ind_name, ind_ml_name) :: names)
     end) (ind_bodies mib) true [];;

  pop_indent;;

  ret names.

Definition print_global_decl
           (name : kername)
           (decl : Ex.global_decl) : PrettyPrinter (list (kername * string)) :=
  match decl with
  | Ex.ConstantDecl cst => ml_name <- print_constant_body name cst;;
                           ret [(name, ml_name)]
  | Ex.InductiveDecl mib => print_mutual_inductive_body name mib
  end.

Definition print_env : PrettyPrinter (list (kername * string)) :=
  sig_col <- get_current_line_length;;
  push_indent sig_col;;

  names <- (fix f (l : Ex.global_env) (first : bool) (names : list (kername * string)) :=
     match l with
     | [] => ret names
     | (name, decl) :: l =>

       (if first then ret tt else (append_nl;; append_nl_and_indent));;
       new_names <- print_global_decl name decl;;

       f l false (new_names ++ names)%list
     end) Σ true [];;

  pop_indent;;

  ret names.
End FixExEnv.

From Coq Require Import ZArith.

Section Counter.
Context `{ChainBase}.
Inductive Msg :=
| increment
| decrement.

Global Instance Serializable_Msg : Serializable Msg :=
  Derive Serializable Msg_rect<increment, decrement>.

Local Open Scope Z.
Definition init
           (chain : Chain)
           (ctx : ContractCallContext)
           (setup : unit) : option Z :=
  Some 0%Z.

Definition receive
           (chain : Chain)
           (ctx : ContractCallContext)
           (state : Z)
           (maybe_msg : option Msg)
  : option (Z * list ActionBody) :=
  match maybe_msg with
  | Some increment => Some (state + 1, [])
  | Some decrement => Some (state - 1, [])
  | _ => None
  end.

Program Definition contract : Contract unit Msg Z :=
  {| Blockchain.init := init; Blockchain.receive := receive; |}.

End Counter.

Definition foo : TemplateMonad unit :=
  s <- get_contract_extraction_set (fun cb => @contract cb);;
  result <- tmEval lazy (finish_print (print_env (env s)));;
  match result with
  | Ok (name_map, result) => tmMsg result
  | Err s => tmFail s
  end.

Run TemplateProgram foo.

Quote Recursively Definition ex6 := (forall (A : Type), A -> forall (B : Type), B -> nat).
Compute erase_type_program ex6.
Compute erase_and_print_type debox_box_type ex6.


Quote Recursively Definition test_program := (init).

Definition ignored_concert_types :=
  ["ConCert.Execution.Blockchain.ChainBase";
   "ConCert.Execution.Blockchain.Chain";
   "ConCert.Execution.Blockchain.ContractCallContext"].

Compute erase_and_debox_template_program test_program ignored_concert_types.

Run TemplateProgram foo.

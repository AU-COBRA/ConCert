From ConCert.Execution Require Import Blockchain.
From ConCert.Execution Require Import Serializable.
From ConCert.Execution Require Import Containers.
From ConCert.Extraction Require Import Common.
From ConCert.Extraction Require Import Erasure.
From ConCert.Extraction Require Import Extraction.
From ConCert.Extraction Require Import SpecializeChainBase.
From ConCert.Extraction Require Import ExAst.
From ConCert.Extraction Require Import Optimize.
From ConCert.Extraction Require Import PrettyPrinterMonad.
From ConCert.Extraction Require Import ResultMonad.
From ConCert.Extraction Require Import StringExtra.

From Coq Require Import Arith.
From Coq Require Import Ascii.
From Coq Require Import List.
From Coq Require Import NArith.
From Coq Require Import PArith.
From Coq Require Import String.
From Coq Require Import ZArith.

From MetaCoq.SafeChecker Require Import PCUICSafeChecker SafeTemplateChecker.
From MetaCoq.Template Require Import All.
From MetaCoq.Erasure Require Import Loader SafeTemplateErasure EAst EAstUtils ETyping.

Import StringExtra.

Module P := MetaCoq.PCUIC.PCUICAst.
Module PT := MetaCoq.PCUIC.PCUICTyping.
Module T2P := MetaCoq.PCUIC.TemplateToPCUIC.
Module E := MetaCoq.Erasure.EAst.
Module T := MetaCoq.Template.Ast.
Module TUtil := MetaCoq.Template.AstUtils.
Module EF := MetaCoq.Erasure.SafeErasureFunction.
Module Ex := ConCert.Extraction.ExAst.

Import PrettyPrinterMonad.
Import ListNotations.
Import MonadNotation.

Local Open Scope list.
Local Open Scope string.

Local Definition indent_size := 2.

Section FixEnv.
  Context (Σ : Ex.global_env).
(* Additional environment only used to look up names for inductives
   and inductive ctors. Those names are required to be translated
   or the printing will fail. *)
Context (Σnames : T.global_env).
Context (translate : kername -> option string).
(* A setting for symbols for boxes and un-extractable types *)
Class BoxSymbol :=
  {term_box_symbol : string;
   type_box_symbol : string;
   any_type_symbol : string}.

Context `{BoxSymbol}.

Definition option_get {A} (o : option A) (default : A) : A :=
  match o with
  | Some a => a
  | None => default
  end.

Definition get_fun_name (name : kername) : string :=
  option_get
    (translate name)
    (uncapitalize (replace_char "." "_" name.2)).

Definition get_ty_name (name : kername) : string :=
  option_get
    (translate name)
    (capitalize (replace_char "." "_" name.2)).

Definition get_ctor_name (name : kername) : string :=
  option_get
    (translate name)
    (capitalize name.2).

Definition get_ident_name (name : ident) : string :=
  uncapitalize (remove_char "'" (replace_char "." "_" name)).

Definition get_ty_arg_name (name : ident) : ident :=
  uncapitalize name.

Definition lookup_mind (name : kername) : option Ex.mutual_inductive_body :=
  match Ex.lookup_env Σ name with
  | Some (Ex.InductiveDecl _ mib) => Some mib
  | _ => None
  end.

Definition lookup_ind_decl (ind : inductive) : result Ex.one_inductive_body string :=
  match Ex.lookup_env Σ (inductive_mind ind) with
  | Some (Ex.InductiveDecl _ {| Ex.ind_bodies := oibs |}) =>
    match nth_error oibs (inductive_ind ind) with
    | Some body => ret body
    | None => Err ("Could not find inductive "
                     ++ string_of_nat (inductive_ind ind)
                     ++ " in mutual inductive " ++ string_of_kername (inductive_mind ind))
    end
  | _ => Err ("Could not find inductive "
                ++ string_of_kername (inductive_mind ind) ++ " in environment")
  end.

Definition names_lookup_ind_decl (ind : inductive) : option T.one_inductive_body :=
  match T.lookup_env Σnames (inductive_mind ind) with
  | Some (T.InductiveDecl {| T.ind_bodies := oibs |}) =>
    nth_error oibs (inductive_ind ind)
  | _ => None
  end.

Definition print_ind (ind : inductive) : PrettyPrinter unit :=
  match lookup_ind_decl ind with
  | Ok oib =>
    let kn := ((inductive_mind ind).1, Ex.ind_name oib) in
    append (get_ty_name kn)
  | Err err =>
    (* Not found in extraction environment, lookup in names environment *)
    match names_lookup_ind_decl ind with
    | Some oib =>
      let kn := ((inductive_mind ind).1, T.ind_name oib) in
      (* We require this to be translated now *)
      append =<< wrap_option (translate kn) ("No translation for " ++ string_of_kername kn)
    | None => printer_fail err
    end
  end.

Definition print_ind_ctor (ind : inductive) (i : nat) : PrettyPrinter unit :=
  match lookup_ind_decl ind with
  | Ok oib =>
    match nth_error (Ex.ind_ctors oib) i with
    | Some (name, _) =>
      let kn := ((inductive_mind ind).1, name) in
      append (get_ctor_name kn)
    | None =>
      printer_fail (Ex.ind_name oib ++ " does not have a ctor " ++ string_of_nat i)
    end
  | Err err =>
    match names_lookup_ind_decl ind with
    | Some oib =>
      match nth_error (T.ind_ctors oib) i with
      | Some (name, _, _) =>
        let kn := ((inductive_mind ind).1, name) in
        append =<< wrap_option (translate kn) ("No translation for " ++ string_of_kername kn)
      | None =>
        printer_fail (T.ind_name oib ++ " does not have a ctor " ++ string_of_nat i)
      end
    | _ => printer_fail err
    end
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
  | nAnon => ret (fresh "x" (Γ ++ used_names))
  | nNamed name => ret (fresh (get_ident_name name) (Γ ++ used_names))
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
  | TBox => append type_box_symbol
  | TAny => append any_type_symbol
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
  | TVar n =>
    match nth_error Γ n with
    | Some name => append name
    | None => printer_fail ("unbound TVar " ++ string_of_nat n)
    end
  | TInd ind => print_ind ind
  | TConst name => append (get_ty_name name)
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
  | tBox => append term_box_symbol
  | tRel n =>
    match nth_error Γ n with
    | Some name => append name
    | None => printer_fail ("unbound tRel " ++ string_of_nat n)
    end
  | tVar ident => printer_fail ("tVar " ++ ident)
  | tEvar _ _ => printer_fail "unexpected evar"
  | tLambda name t =>

    append "\";;

    (fix f Γ name body :=
       name <- fresh_ident name Γ;;
       append (name ++ " ");;

       let Γ := name :: Γ in
       match body with
       | tLambda name t => f Γ name t
       | _ => append "-> ";; print_term Γ body
       end) Γ name t

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

  | tCase (ind, npars) discriminee branches =>
    case_col <- get_current_line_length;;
    append "case ";;
    print_parenthesized (parenthesize_case_discriminee discriminee)
                        (print_term Γ discriminee);;
    append " of";;

    push_indent (case_col + indent_size);;

    oib <- wrap_result (lookup_ind_decl ind) id;;

    (* Take care that this is structurally recursive... *)
    (fix print_branches
         (branches : list (nat * term))
         (ctors : list (ident * list Ex.box_type)) :=
       match branches, ctors with
       | [], [] => ret tt
       | (arity, t) :: branches, (ctor_name, data) :: ctors =>
         append_nl_and_indent;;

         ctor_indent <- get_indent;;
         push_indent (ctor_indent + indent_size);;

         append (get_ctor_name ((inductive_mind ind).1, ctor_name));;

         (* In Coq, parameters are not part of branches. But erasure
            adds the parameters to each constructor, so we need to get those
            out of the way first. These won't have any uses so we just print _. *)
         append (concat "" (map (fun _ => " _") (seq 0 npars)));;

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

         print_branches branches ctors
       | _, _ => printer_fail "wrong number of case branches compared to inductive"
       end) branches (Ex.ind_ctors oib);;

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

Definition print_constant
           (kn : kername)
           (type : (list name × box_type))
           (body : E.term) : PrettyPrinter string :=

  let ml_name := get_fun_name kn in

  name_col <- get_current_line_length;;
  push_indent name_col;;

  match type with
  | (type_vars, ty) =>
    append ml_name;;
    append " : ";;
    Γrev <- monad_fold_left (fun Γ name => name <- fresh_ty_arg_name name Γ;;
                                           ret (name :: Γ))
                            type_vars [];;
    print_type (rev Γrev) ty;;
    append_nl_and_indent
  end;;

  push_use ml_name;;
  print_define_term [] ml_name body print_term;;
  pop_indent;;

  ret ml_name.

Import P.
Definition parenthesize_ind_ctor_ty (ty : box_type) : bool :=
  match ty with
  | TBox
  | TAny
  | TVar _
  | TInd _
  | TConst _ => false
  | _ => true
  end.

Definition print_ind_ctor_definition
           (Γ : list ident)
           (name : kername)
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
           (kn : kername)
           (mib : mutual_inductive_body) : PrettyPrinter (list (kername * string)) :=
  col <- get_current_line_length;;
  push_indent col;;

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
       Γ <- monad_fold_left
              (fun Γ name =>
                 name <- fresh_ty_arg_name (tvar_name name) Γ;;
                 ret (Γ ++ [name])%list) (ind_type_vars oib) [];;

       append "type ";;
       let ind_name := (kn.1, ind_name oib) in
       let ind_ml_name := get_ty_name ind_name in
       append ind_ml_name;;

       (* Print type args *)
       monad_fold_left (fun _ name => append (" " ++ name)) Γ tt;;

       push_indent (col + indent_size);;

       (* Type variables for constructors *)
       Γc <- monad_fold_left
              (fun Γ name =>
                 name <- fresh_ty_arg_name (tvar_name name) Γ;;
                 ret (Γ ++ [name])%list) (ind_ctor_type_vars oib) [];;


       (fix print_ind_ctors (ctors : list (ident * list box_type)) prefix :=
          match ctors with
          | [] => ret tt
          | (name, data) :: ctors =>
            append_nl_and_indent;;
            append (prefix ++ " ");;
            print_ind_ctor_definition Γc (kn.1, name) data;;

            print_ind_ctors ctors "|"
          end) (ind_ctors oib) "=";;

       pop_indent;;

       print_ind_bodies l false ((ind_name, ind_ml_name) :: names)
     end) (ind_bodies mib) true [];;

  pop_indent;;

  ret names.

Definition print_type_alias
           (nm : kername)
           (ty : list name × Ex.box_type) : PrettyPrinter string :=
  append "type alias ";;
  let ty_ml_name := get_ty_name nm in
  append ty_ml_name;;
  let '(type_vars, ty) := ty in
  append " = ";;
  Γrev <- monad_fold_left (fun Γ name => name <- fresh_ty_arg_name name Γ;;
                                           ret (name :: Γ))
                         type_vars [];;
  (* FIXME: print type vars? Can type aliases have parameters? *)
  print_type (rev Γrev) ty ;;
  append_nl ;;
  ret ty_ml_name.

Definition print_env : PrettyPrinter (list (kername * string)) :=
  sig_col <- get_current_line_length;;
  push_indent sig_col;;

  names <- (fix f l prefix names :=
     match l with
     | [] => ret names
     | (kn, decl) :: l =>
       new_names <-
       match decl with
       | Ex.ConstantDecl {|
             Ex.cst_type := type;
             Ex.cst_body := Some body; |} =>
         prefix;;
         name <- print_constant kn type body;;
         ret [(kn, name)]
       | Ex.InductiveDecl false mib =>
         prefix;;
         print_mutual_inductive_body kn mib
       | Ex.TypeAliasDecl ty =>
         prefix;;
         name <- print_type_alias kn ty;;
         ret [(kn, name)]
       | _ => ret []
       end;;

       f l (append_nl;; append_nl_and_indent) (new_names ++ names)%list
     end) (List.rev Σ) (ret tt) [];;

  pop_indent;;

  ret names.
End FixEnv.

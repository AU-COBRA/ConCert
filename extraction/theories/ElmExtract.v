From MetaCoq.Template Require Import monad_utils.
From MetaCoq.TypedExtraction Require Import Extraction.
From MetaCoq.TypedExtraction Require Import ExAst.
From MetaCoq.TypedExtraction Require Import ResultMonad.
From ConCert.Utils Require Import StringExtra.
From ConCert.Extraction Require Import Common.
From ConCert.Extraction Require Import PrettyPrinterMonad.
From Coq Require Import Ascii.
From Coq Require Import String.
From Coq Require Import List.

Import ListNotations.
Import MCMonadNotation.
Import PrettyPrinterMonad.

Module P := MetaCoq.PCUIC.PCUICAst.
Module PT := MetaCoq.PCUIC.PCUICTyping.
Module T2P := MetaCoq.PCUIC.TemplateToPCUIC.
Module E := MetaCoq.Erasure.EAst.
Module T := MetaCoq.Template.Ast.
Module TUtil := MetaCoq.Template.AstUtils.
Module EF := MetaCoq.Erasure.ErasureFunction.
Module Ex := MetaCoq.TypedExtraction.ExAst.

Local Open Scope string.

Local Definition indent_size := 2.

Import Kernames.

Section FixEnv.
Context (Σ : Ex.global_env).
Context (translate : kername -> option string).

Local Open Scope string_scope.
Local Notation bs_to_s := bytestring.String.to_string.
Local Notation s_to_bs := bytestring.String.of_string.
Local Coercion bytestring.String.to_string : bytestring.string >-> string.

Local Infix "^" := String.append.


(** A printing config for Elm *)
Class ElmPrintConfig :=
  { term_box_symbol : string;
    type_box_symbol : string;
    any_type_symbol : string;
    false_elim_def : string;
    print_full_names : bool (* use fully-qualified names as identifiers to avoid name clashes *) }.

(** A default false_elim implementation as a forever spinning loop *)
Definition elm_false_rec :=
  String.concat nl
                ["false_rec : () -> a";
                "false_rec _ = false_rec ()"].


Context `{ElmPrintConfig}.

Import MCOption.

Definition get_fun_name (name : kername) : string :=
  let get_name kn := if print_full_names then
                       replace_char "." "_" (string_of_kername name)
                     else (snd name) in
  option_get
    (uncapitalize (get_name name))
    (translate name).

Definition get_ty_name (name : kername) : string :=
  option_get
    (capitalize (replace_char "." "_" (snd name)))
    (translate name).

Definition get_ctor_name (name : kername) : string :=
  option_get
    (capitalize (snd name))
    (translate name).

Definition get_ident_name (name : ident) : ident :=
  s_to_bs (uncapitalize (remove_char "'" (replace_char "." "_" name))).

Definition get_ty_arg_name (name : ident) : ident :=
  s_to_bs (uncapitalize name).

Definition lookup_mind (name : kername) : option Ex.mutual_inductive_body :=
  match Ex.lookup_env Σ name with
  | Some (Ex.InductiveDecl mib) => Some mib
  | _ => None
  end.

Definition lookup_ind_decl (ind : inductive) : result Ex.one_inductive_body string :=
  match Ex.lookup_env Σ (inductive_mind ind) with
  | Some (Ex.InductiveDecl {| Ex.ind_bodies := oibs |}) =>
    match nth_error oibs (inductive_ind ind) with
    | Some body => ret body
    | None => Err ("Could not find inductive "
                     ^ string_of_nat (inductive_ind ind)
                     ^ " in mutual inductive " ^ string_of_kername (inductive_mind ind))
    end
  | _ => Err ("Could not find inductive "
                ^ string_of_kername (inductive_mind ind) ^ " in environment")
  end.

Definition print_ind (ind : inductive) : PrettyPrinter unit :=
  oib <- wrap_result (lookup_ind_decl ind) id;;
  let kn := (fst (inductive_mind ind), Ex.ind_name oib) in
  append (get_ty_name kn).

Definition print_ind_ctor (ind : inductive) (i : nat) : PrettyPrinter unit :=
  oib <- wrap_result (lookup_ind_decl ind) id;;
  match nth_error (Ex.ind_ctors oib) i with
  | Some (name, _, _) =>
    let kn := (fst (inductive_mind ind), name) in
    append (get_ctor_name kn)
  | None =>
    printer_fail (Ex.ind_name oib ^ " does not have a ctor " ^ string_of_nat i)
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

(* TODO: move to printing utils *)
Definition fresh (name : ident) (used : list ident) : ident :=
  if existsb (bytestring.String.eqb name) used then
    (fix f n i :=
       match n with
       | 0 => s_to_bs "unreachable"
       | S n =>
         let numbered_name := bytestring.String.append name (MCString.string_of_nat i) in
         if existsb (bytestring.String.eqb numbered_name) used then
           f n (S i)
         else
           numbered_name
       end) (S (List.length used)) 2
  else
    name.

Import BasicAst.

Definition fresh_ident (name : name) (Γ : list ident) : PrettyPrinter ident :=
  used_names <- get_used_names;;
  match name with
  | nAnon => ret (fresh (s_to_bs "x") (Γ ++ used_names))
  | nNamed name => ret (fresh (get_ident_name name) (Γ ++ used_names))
  end.

Definition fresh_ty_arg_name (name : name) (Γ : list ident) : PrettyPrinter ident :=
  used_names <- get_used_names;;
  match name with
  | nAnon => ret (fresh (s_to_bs "a") (Γ ++ used_names))
  | nNamed name => ret (fresh (get_ty_arg_name name) (Γ ++ used_names))
  end.

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
    | None => printer_fail ("unbound TVar " ^ string_of_nat n)
    end
  | TInd ind => print_ind ind
  | TConst name => append (get_ty_name name)
  end.

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
        append (" " ^ arg_name);;
        print_decompose (arg_name :: Γ) t
      | _ =>
        append " =";;
        push_indent (name_col + indent_size);;
        append_nl;;
        print_term Γ t;;
        pop_indent
      end in

  match t with
  | tFix [d] 0 => print_decompose (name :: Γ) (EAst.dbody d)
  | _ => print_decompose Γ t
  end.

Local Open Scope bool.

(* TODO: Eventually, we might want to include some checks is the operators actually meets the syntactic creteria of Elm *)
Definition get_infix (s : string) : option string :=
  let len := String.length s in
  let begins := substring_count 1 s in
  let ends := substring_from (len - 1) s in
  if (begins =? "(") && (ends =? ")") then
    Some (substring 1 (len-2) s)
  else
    None.

(** Print a constructor as an infix operatior in patterns.

   E.g. for [infix_op = "::"] it expects the branch context contains
   two names (the context is reversed)
   [nNamed "xs", nNamed "x"],
   so the corresponding pattern will look like [x :: xs => ...] *)
Definition print_infix_match_branch (print : list ident -> term -> PrettyPrinter unit) (infix_op : string) (Γ : list ident) (br_ctx : list name) (br : term) :=
  match br_ctx with
    | [name2; name1] =>
      name1 <- fresh_ident name1 Γ;;
      let Γ := name1 :: Γ in
      name2 <- fresh_ident name2 Γ;;
      append (name1 ^ " ");;
      append infix_op;;
      append (" " ^ name2);;
      append " ->";;
      append_nl;;
      print_parenthesized (parenthesize_case_branch br) (print (name2 :: Γ) br)
    | _ => printer_fail "could not decompose branch for infix constructor"
  end.

Fixpoint print_term (Γ : list ident) (t : term) : PrettyPrinter unit :=
  match t with
  | tBox => append term_box_symbol
  | tRel n =>
    match nth_error Γ n with
    | Some name => append name
    | None => printer_fail ("unbound tRel " ^ string_of_nat n)
    end
  | tVar ident => printer_fail ("tVar " ^ ident)
  | tEvar _ _ => printer_fail "unexpected evar"
  | tLambda name t =>

    append "\";;

    (fix f Γ name body :=
       name <- fresh_ident name Γ;;
       append (name ^ " ");;

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
        append_nl;;
        name <- fresh_ident name Γ;;
        (* We will define this name to make sure we don't reuse it
           until the let is all over. Elm does not allow shadowing. *)
        push_use name;;
        print_define_term Γ name value print_term;;
        ret (name :: Γ) in

    push_indent (let_col + indent_size);;

    Γ <- print_and_add_one Γ name value;;

    (* Print in Elm style, which collapses multiple lets into one *)
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

         append_nl;; (* indent to 'let' keyword *)
         append "in";;

         append_nl;; (* body is indented to 'let'/'in' keyword as well *)
         print_term Γ t;;
         pop_indent;;
         ret 0
       end) Γ body;;

    (* pop all the names we defined, we can reuse those names now. *)
    monad_fold_left (fun _ _ => pop_use) (repeat tt (S num_collapsed)) tt
    *)

    pop_indent;;
    append_nl;;

    append "in";;
    append_nl;;
    print_term Γ body;;
    pop_indent;;

    pop_use

  | tApp head arg =>
    print_parenthesized (parenthesize_app_head head) (print_term Γ head);;
    append " ";;
    print_parenthesized (parenthesize_app_arg arg) (print_term Γ arg)

  | tConst name => append (get_fun_name name)
  | tConstruct ind i [] => print_ind_ctor ind i
  | tConstruct ind i (_ :: _) =>
           printer_fail ("Costructors-as-blocks is not supported: "
                         ^ bs_to_s (string_of_kername ind.(inductive_mind)))

  | tCase (ind, npars) discriminee branches =>
    match branches with
    | [] => append false_elim_def
    | _ =>
      case_col <- get_current_line_length;;
      append "case ";;
      print_parenthesized (parenthesize_case_discriminee discriminee)
                          (print_term Γ discriminee);;
      append " of";;

      push_indent (case_col + indent_size);;

      oib <- wrap_result (lookup_ind_decl ind) id;;

    (* Take care that this is structurally recursive... *)
      (fix print_branches
           (branches : list (list name * term))
           (ctors : list (ident * list (name * Ex.box_type) * nat)) :=
         match branches, ctors with
         | [], [] => ret tt
         | (bctx, t) :: branches, (ctor_name, data, _) :: ctors =>
           append_nl;;

           ctor_indent <- get_indent;;
           push_indent (ctor_indent + indent_size);;

           let ctor_name := get_ctor_name (fst (inductive_mind ind), ctor_name) in
           (* NOTE: if the constructor name is some operator in parenthesis, we apply a special prining procedure for infix constructors *)
           match get_infix ctor_name with
           | Some op => print_infix_match_branch print_term op Γ bctx t
           | None =>
             append (get_ctor_name (fst (inductive_mind ind), s_to_bs ctor_name));;

             (* In Coq, parameters are not part of branches. But erasure
            adds the parameters to each constructor, so we need to get those
            out of the way first. These won't have any uses so we just print _. *)
             append (String.concat "" (map (fun _ => " _") (seq 0 npars)));;

             (fix print_branch (bctx : list name) (args : list ident) (Γ : list ident) :=
                match bctx with
                | [] =>
                  append " ->";;
                  append_nl;;
                  print_parenthesized (parenthesize_case_branch t) (print_term Γ t)

                | name :: bctx0 =>
                    name <- fresh_ident name Γ;;
                    append (" " ^ name);;
                    print_branch bctx0 (name :: args) (name :: Γ)
                end) (List.rev bctx) [] Γ
           end;;

           pop_indent;;
           print_branches branches ctors
       | _, _ => printer_fail "wrong number of case branches compared to inductive"
       end) branches (Ex.ind_ctors oib);;

      pop_indent
    end

  | tProj _ _ => printer_fail "tProj"

  | tFix mfix nfix =>
    let_col <- get_current_line_length;;
    push_indent let_col;;

    (* Add names of fixes to context *)
    Γ <- monad_fold_left
           (fun Γ d => name <- fresh_ident (EAst.dname d) Γ;;
                       ret (name :: Γ)) mfix Γ;;
    let names := rev (firstn (List.length mfix) Γ) in

    append "let";;

    push_indent (let_col + indent_size);;

    (fix print_fixes (ds : list (EAst.def term)) (names : list ident) :=
       match ds, names with
       | [], _ => ret tt
       | d :: ds, name :: names =>
         append_nl;;
         print_define_term Γ name (EAst.dbody d) print_term;;
         print_fixes ds names
       | _, _ =>
         printer_fail "unreachable"
       end) mfix names;;

    pop_indent;;

    append_nl;;
    append "in";;
    append_nl;;
    match nth_error names nfix with
    | Some n => append n
    | None => printer_fail "invalid fix index"
    end;;

    pop_indent

  | tCoFix _ _ => printer_fail "Cannot handle cofix"
  (* | tPrim _ => printer_fail "Cannot handle Coq primitive types" *)
  end.

Definition print_constant
           (kn : kername)
           (type : (list name * box_type))
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
    append_nl
  end;;

  print_define_term [] (s_to_bs ml_name) body print_term;;
  pop_indent;;

  ret ml_name.

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
           (ctor_name : kername)
           (data : list (name * box_type)) : PrettyPrinter unit :=
  append (get_ctor_name ctor_name);;

  monad_fold_left (fun _ '(_, bty) =>
                     append " ";;
                     print_parenthesized
                       (parenthesize_ind_ctor_ty bty)
                       (print_type Γ bty)) data tt.

Local Open Scope string.
Import ExAst PrettyPrinterMonad.
Definition print_mutual_inductive_body
           (kn : kername)
           (mib : mutual_inductive_body) : PrettyPrinter (list (kername * string)) :=
  col <- get_current_line_length;;
  push_indent col;;

  names <-
  (fix print_ind_bodies
       (l : list one_inductive_body)
       (first : bool)
       (names : list (kername * string)) : PrettyPrinter (list (kername * string)) :=
     match l with
     | [] => ret names
     | oib :: l =>

       (if first then ret tt else append_nl);;

       (* Add type parameters. Note that since we are in prenex form, *)
       (* our context will have last type parameter last, not first. *)
       Γ <- monad_fold_left
              (fun Γ name =>
                 name <- fresh_ty_arg_name (tvar_name name) Γ;;
                 ret (Γ ++ [name])%list) (Ex.ind_type_vars oib) [];;

       append "type ";;
       let ind_name := (fst kn, ind_name oib) in
       let ind_ml_name := get_ty_name ind_name in
       append ind_ml_name;;

       (* Print type args *)
       monad_fold_left (fun _ name => append (" " ^ name)) (map bs_to_s Γ) tt;;

       push_indent (col + indent_size);;

       (fix print_ind_ctors (ctors : list (ident * list (name * box_type) * nat)) prefix :=
          match ctors with
          | [] => ret tt
          | (name, data, _) :: ctors =>
            append_nl;;
            append (prefix ^ " ");;
            print_ind_ctor_definition Γ (fst kn, name) data;;

            print_ind_ctors ctors "|"
          end) (ind_ctors oib) "=";;

       pop_indent;;

       print_ind_bodies l false ((ind_name, ind_ml_name) :: names)
     end) (ind_bodies mib) true [];;

  pop_indent;;

  ret names.

Definition print_type_alias
           (nm : kername)
           (tvars : list type_var_info)
           (bt : box_type) : PrettyPrinter string :=
  append "type alias ";;
  let ty_ml_name := get_ty_name nm in
  append ty_ml_name;;
  Γrev <- monad_fold_left (fun Γ tvar => name <- fresh_ty_arg_name (tvar_name tvar) Γ;;
                                         ret (name :: Γ))
                          tvars [];;
  let Γ := rev Γrev in
  append (String.concat "" (map (fun x => " " ^ x) (map bs_to_s Γ)));;
  append " = ";;
  print_type Γ bt;;
  ret ty_ml_name.

Definition print_env : PrettyPrinter (list (kername * string)) :=
  monad_iter push_use (map (fun '(kn, _, _) => s_to_bs (get_fun_name kn)) Σ);;
  sig_col <- get_current_line_length;;
  push_indent sig_col;;

  (* Filtering out empty type declarations *)
  (* TODO: possibly, move to extraction (requires modifications of the correctness proof) *)
  let Σ := filter (fun '(kn,d) => negb (is_empty_type_decl d)) Σ in

  names <- (fix f (l : list (kername * bool * global_decl)) prefix names :=
     match l with
     | [] => ret names
     | (kn, has_deps, decl) :: l =>

       new_names <-
       (if has_deps then
         match decl with
         | Ex.ConstantDecl {|
               Ex.cst_type := type;
               Ex.cst_body := Some body; |} =>
           prefix;;
           name <- print_constant kn type body;;
           ret [(kn, name)]
         | Ex.InductiveDecl mib =>
           prefix;;
           print_mutual_inductive_body kn mib
         | Ex.TypeAliasDecl (Some (tvars, bt)) =>
           prefix;;
           name <- print_type_alias kn tvars bt;;
           ret [(kn, name)]
         | _ => ret []
         end
       else
         ret []);;

       f l (append_nl;; append_nl) (new_names ++ names)%list
     end) (List.rev Σ) (ret tt) [];;

  pop_indent;;

  ret names.
End FixEnv.

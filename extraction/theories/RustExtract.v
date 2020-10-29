From ConCert.Execution Require Import Blockchain.
From ConCert.Execution Require Import Serializable.
From ConCert.Execution Require Import Containers.
From ConCert.Extraction Require Import Common.
From ConCert.Extraction Require Import Erasure.
From ConCert.Extraction Require Import ExAst.
From ConCert.Extraction Require Import Extraction.
From ConCert.Extraction Require Import Optimize.
From ConCert.Extraction Require Import PrettyPrinterMonad.
From ConCert.Extraction Require Import ResultMonad.
From ConCert.Extraction Require Import StringExtra.
From ConCert.Extraction Require Import TopLevelFixes.

From Coq Require Import Arith.
From Coq Require Import Ascii.
From Coq Require Import List.
From Coq Require Import NArith.
From Coq Require Import PArith.
From Coq Require Import String.
From Coq Require Import ZArith.

From MetaCoq.SafeChecker Require Import PCUICSafeChecker SafeTemplateChecker.
From MetaCoq.Template Require Import Kernames All.
From MetaCoq.Erasure Require Import Loader SafeTemplateErasure EAst EAstUtils ELiftSubst ETyping.

Import StringExtra.
Import String.
Import PrettyPrinterMonad.

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
Context (translate : kername -> option string).
(* A printing config for Rust *)
Class RustPrintConfig :=
  { term_box_symbol : string;
    type_box_symbol : string;
    any_type_symbol : string;
    print_full_names : bool (* use fully-qualified names as identifiers to avoid name clashes *)}.

Context `{RustPrintConfig}.

Definition option_get {A} (o : option A) (default : A) : A :=
  match o with
  | Some a => a
  | None => default
  end.

Definition get_const_name (name : kername) : string :=
  let const_name :=
      if print_full_names then
        replace_char "." "_" (string_of_kername name)
      else
        name.2 in
  option_get (translate name) const_name.

Definition get_ty_name (name : kername) : string :=
  capitalize (option_get (translate name) (replace_char "." "_" name.2)).

Definition get_ctor_name (name : kername) : string :=
  capitalize (option_get (translate name) name.2).

Definition get_ident_name (name : ident) : string :=
  remove_char "'" (replace_char "." "_" name).

Definition get_ty_arg_name (name : ident) : ident :=
  name.

Definition is_polymorphic (cst : Ex.constant_body) : bool :=
  0 <? #|(Ex.cst_type cst).1|.

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
                     ++ string_of_nat (inductive_ind ind)
                     ++ " in mutual inductive " ++ string_of_kername (inductive_mind ind))
    end
  | _ => Err ("Could not find inductive "
                ++ string_of_kername (inductive_mind ind) ++ " in environment")
  end.

Definition print_ind (ind : inductive) : PrettyPrinter unit :=
  oib <- wrap_result (lookup_ind_decl ind) id;;
  let kn := ((inductive_mind ind).1, Ex.ind_name oib) in
  append (get_ty_name kn).

Definition print_ind_ctor (ind : inductive) (i : nat) : PrettyPrinter unit :=
  oib <- wrap_result (lookup_ind_decl ind) id;;
  match nth_error (Ex.ind_ctors oib) i with
  | Some (name, _) =>
    let kn := ((inductive_mind ind).1, name) in
    print_ind ind;;
    append ("::" ++ get_ctor_name kn)
  | None =>
    printer_fail (Ex.ind_name oib ++ " does not have a ctor " ++ string_of_nat i)
  end.

Definition print_parenthesized
           (parenthesize : bool)
           (print : PrettyPrinter unit) : PrettyPrinter unit :=
  if parenthesize then
    append "(";; print;; append ")"
  else
    print.

Definition print_parenthesized_with par_start par_end :=
  fun (parenthesize : bool) (print : PrettyPrinter unit) =>
  if parenthesize then append par_start;; print;; append par_end else print.


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

Definition parenthesize_ty_app_arg (t : box_type) : bool :=
  match t with
  | TApp _ _ => true
  | _ => false
  end.

Fixpoint print_type_aux (Γ : list ident) (t : box_type) (args : list (PrettyPrinter unit)) :=
  match t with
  | TBox => append type_box_symbol
  | TAny => append any_type_symbol
  | TArr dom cod =>
    append "&'a dyn Fn(";;
    print_type_aux Γ dom [];;
    append ") -> ";;
    print_type_aux Γ cod []
  | TApp head arg =>
    print_type_aux Γ head (print_type_aux Γ arg [] :: args)
  | TVar n =>
    match nth_error Γ n with
    | Some name => append name
    | None => printer_fail ("unbound TVar " ++ string_of_nat n)
    end
  | TInd ind =>
    append "&'a ";;
    print_ind ind;;
    append "<";;
    monad_append_join (append ", ") (append "'a" :: args);;
    append ">"

  | TConst name =>
    append (get_ty_name name ++ "<");;
    monad_append_join (append ", ") (append "'a" :: args);;
    append ">"
  end.

Definition print_type Γ t := print_type_aux Γ t [].

(* Get number of arguments that a constant expects when we print it *)
Definition get_num_inline_args (kn : kername) : PrettyPrinter nat :=
  cst <- wrap_option
           (Ex.lookup_constant Σ kn)
           ("Could not find constant " ++ string_of_kername kn);;
  match Ex.cst_body cst with
  | None => ret #|(decompose_arr (Ex.cst_type cst).2).1|
  | Some body =>
    let fix count body ty :=
        match body, ty with
        | tLambda _ body, TArr dom cod => S (count body cod)
        | _, _ => 0
        end in
    ret (count body (Ex.cst_type cst).2)
  end.

Definition bracketize_let_value (t : term) :=
  match t with
  | tFix _ _
  | tLetIn _ _ _ => true
  | _ => false
  end.

Fixpoint print_term (Γ : list ident) (t : term) {struct t} : PrettyPrinter unit :=
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
    name <- fresh_ident name Γ;;
    col <- get_current_line_length;;
    push_indent col;;
    append ("self.closure(move |" ++ name ++ "| {");;

    push_indent (col + indent_size);;
    append_nl_and_indent;;
    let Γ := name :: Γ in
    print_term Γ t;;
    pop_indent;;
    append_nl_and_indent;;
    append "})";;
    pop_indent

  | tLetIn na val body =>
    name <- fresh_ident na Γ;;
    col <- get_current_line_length;;

    push_indent col;;
    append ("let " ++ name ++ " =");;
    (if bracketize_let_value val then append " {" else ret tt);;

    push_indent (col + indent_size);;
    append_nl_and_indent;;
    print_term Γ val;;
    pop_indent;;

    (if bracketize_let_value val then
       append_nl_and_indent;;
       append "};"
     else
       append ";");;

    append_nl_and_indent;;

    print_term (name :: Γ) body;;
    pop_indent

  | tApp head arg =>

    (fix f head args_printed {struct head} :=
       match head with
       | tApp head arg => f head (print_term Γ arg :: args_printed)
       | tConstruct ind i =>
         append "self.alloc(";;
         print_ind_ctor ind i;;
         append "(";;
         monad_append_join (append ", ") (append "PhantomData" :: args_printed);;
         append "))"

       | tConst kn =>
         num_args <- get_num_inline_args kn;;
         let (name, num_args) :=
             if #|args_printed| <? num_args then
               (* Not enough args, use closure *)
               (get_const_name kn ++ "__closure", 0)
             else
               (get_const_name kn, num_args) in
         append ("self." ++ name ++ "(");;
         monad_append_join
           (append ", ")
           (firstn num_args args_printed);;
         append ")";;
         monad_fold_left
           (fun _ a => append "(";; a;; append ")") (skipn num_args args_printed) tt

       | _ =>
         (* For other heads we might need to guide type inference by repeatedly
            applying a hint function *)
         append (concat "" (repeat "hint_app(" #|args_printed|));;
         print_term Γ head;;
         append ")";;
         monad_fold_left
           (fun pref a => append pref;; a;; append ")";; ret ")(") args_printed "(";;
         ret tt

       end) head [print_term Γ arg]

  | tConst name => append ("self." ++ get_const_name name ++ "()")
  | tConstruct ind i =>
    append "self.alloc(";;
    print_ind_ctor ind i;;
    append "(PhantomData)";;
    append ")"

  | tCase (ind, npars) discr brs =>
    col <- get_current_line_length;;
    push_indent col;;
    append "match ";;
    print_term Γ discr;;
    append " {";;

    oib <- wrap_result (lookup_ind_decl ind) id;;

    push_indent (col + indent_size);;
    (fix print_cases (brs : list (nat × term)) (ctors : list (ident × list box_type)) :=
       match brs, ctors with
       | [], [] => ret tt
       | (arity, t) :: branches, (ctor_name, data) :: ctors =>
         append_nl_and_indent;;

         let kn := ((inductive_mind ind).1, name) in
         append "&";;
         append (get_ty_name ((inductive_mind ind).1, Ex.ind_name oib));;
         append "::";;
         append (get_ctor_name ((inductive_mind ind).1, ctor_name));;

         push_indent (col + 2*indent_size);;
         (fix print_branch (n : nat) (Γ : list ident) (t : term) {struct t} :=
            match n, t with
            | 0, _ =>
              (* In Coq, parameters are not part of branches. But erasure
            adds the parameters to each constructor, so we need to get those
            out of the way first. These won't have any uses so we just print _. *)
              (* In addition, we add a phantom data to make it valid to always have lifetimes.
                 That gives another underscores. *)
              let parameters := List.repeat "_" (S npars) in
              let args := (parameters ++ rev (firstn arity Γ))%list in
              print_parenthesized (0 <? #|args|) (append_join ", " args);;
              append " => {";;
              append_nl_and_indent;;
              print_term Γ t

            | S n, tLambda name t =>
              name <- fresh_ident name Γ;;
              print_branch n (name :: Γ) t
            | _, _ => printer_fail "Could not decompose case branch"
            end) arity Γ t;;

         pop_indent;;
         append_nl_and_indent;;
         append "},";;

         print_cases branches ctors
       | _, _ => printer_fail "wrong number of case branches compared to inductive"
       end) brs (Ex.ind_ctors oib);;

    pop_indent;;
    append_nl_and_indent;;
    append "}";;

    pop_indent

  | tFix defs i =>
    (* Rust does not have recursive closures. Instead, we have to do a trick
       where we recurse through the heap: we first create a cell on the heap
       that will point to the closure. Then, we create the closure that unwraps
       the heap location to get itself. Finally, we put the closure into that heap
       location and it is ready to use. It is complicated by the fact that fix points
       are also mutual and we must create many heap cells before assigning the closures,
       and each closure also needs its own clone of each cell. *)
    col <- get_current_line_length;;
    push_indent col;;

    (* Generate names and allocate cells *)
    '(Γ, cells)
    <- monad_fold_left
         (fun '(Γ, cells) d =>
            (* This is hacky, but instead of putting proper names in the context,
               we put a string that unwraps the cell in the context.
               This is simpler for now, but as a side effect we need to push a use
               since the name won't be in the context. In the future we should unwrap it after the
               first closure or find a better way to handle this. *)
            na <- fresh_ident (dname d) Γ;;
            push_use na;;
            append ("let " ++ na ++ " = self.alloc(std::cell::Cell::new(None));");;
            append_nl_and_indent;;
            ret ((na ++ ".get().unwrap()") :: Γ, na :: cells))
         defs (Γ, []);;

    let cells := rev cells in

    (* Print closures. *)
    monad_fold_left
      (fun _ '(print_def, cell) =>
         append (cell ++ ".set(Some(");;
         push_indent (col + indent_size);;
         append_nl_and_indent;;
         print_def;;
         append "));";;
         pop_indent;;
         append_nl_and_indent)
      (combine
         (map (fun d => print_term Γ (dbody d)) defs)
         cells)
      tt;;

    append (nth i cells "" ++ ".get().unwrap()");;
    pop_indent

  | _ => printer_fail "unhandled"
  end.

Definition print_constant
           (kn : kername)
           (type : (list name × box_type))
           (body : E.term) : PrettyPrinter string :=

  let rname := get_const_name kn in

  name_col <- get_current_line_length;;
  push_indent name_col;;

  let (type_vars, ty) := type in
  Γty <- monad_fold_left (fun Γty name => name <- fresh_ty_arg_name name Γty;;
                                          ret (Γty ++ [name])%list)
                         type_vars [];;

  (* Print version with inlined args *)
  append ("fn " ++ rname);;
  print_parenthesized_with
    "<" ">" (0 <? #|Γty|)
    (append_join ", " (map (fun na => na ++ ": Copy") Γty));;
  append "(&'a self";;

  num_inline_args <-
  (fix print_top Γ body ty :=
     match body, ty with
     | tLambda na body, TArr dom cod =>
       na <- fresh_ident na Γ;;
       append (", " ++ na ++ ": ");;
       print_type Γty dom;;
       num <- print_top (na :: Γ) body cod;;
       ret (S num)
     | _, _ =>
       append ") -> ";;
       print_type Γty ty;;
       append " {";;

       push_indent (name_col + indent_size);;
       append_nl_and_indent;;

       push_use rname;;
       print_term Γ body;;

       pop_indent;;
       append_nl_and_indent;;
       append "}";;
       ret 0
     end) [] body ty;;

  (* Print closure version if there were inlined args *)
  (if 0 <? num_inline_args then
     append_nl_and_indent;;
     append ("fn " ++ rname ++ "__closure");;
     print_parenthesized_with
       "<" ">" (0 <? #|Γty|)
       (append_join ", " (map (fun na => na ++ ": Copy") Γty));;
     append "(&'a self) -> ";;
     print_type Γty ty;;
     append " {";;

     push_indent (name_col + indent_size);;
     append_nl_and_indent;;

     push_use (rname ++ "__closure");;
     eta_term <-
     (fix make_eta_term n body ty :=
        match body, ty with
        | tLambda na body, TArr dom cod =>
          eta_term <- make_eta_term (S n) body cod;;
          ret (tLambda na eta_term)
        | _, _ => ret (mkApps (tConst kn) (rev_map tRel (seq 0 n)))
        end) 0 body ty;;
     print_term [] eta_term;;

     pop_indent;;
     append_nl_and_indent;;
     append "}"
   else
     ret tt);;

  pop_indent;;
  ret rname.

Definition print_ind_ctor_definition
           (Γ : list ident)
           (name : kername)
           (data : list box_type) : PrettyPrinter unit :=
  append (get_ctor_name name);;

  (* Make sure we always take a lifetime parameter in data types *)
  append "(";;

  (* All constructors take a PhantomData as their first argument which ensures that
     Rust does not complained about unused lifetimes/type parameters.
     This phantom type is a 'a lifetimed reference to a tuple of all the type args. *)
  let print_phantom :=
      append "PhantomData<&'a ";;
      (if (#|Γ| =? 0)%nat then
         append "()"
       else
         print_parenthesized (1 <? #|Γ|)%nat (append_join ", " Γ));;
      append ">" in
  let print_datas := print_phantom :: map (print_type Γ) data in
  monad_append_join (append ", ") print_datas;;

  append ")".

Local Open Scope string.
Definition print_mutual_inductive_body
           (kn : kername)
           (mib : Ex.mutual_inductive_body) : PrettyPrinter (list (kername * string)) :=
  col <- get_current_line_length;;
  push_indent col;;

  names <-
  (fix print_ind_bodies
       (l : list Ex.one_inductive_body)
       (prefix : PrettyPrinter unit)
       (names : list (kername * string)) :=
     match l with
     | [] => ret names
     | oib :: l =>

       prefix;;

       append "#[derive(Debug, Copy, Clone)]";;
       append_nl_and_indent;;
       append "pub enum ";;
       let ind_name := (kn.1, Ex.ind_name oib) in
       let ind_ml_name := get_ty_name ind_name in
       append ind_ml_name;;

       (* Add type parameters. Note that since we are in prenex form,
          our context will have last type parameter last, not first. *)
       Γ <- monad_fold_left
              (fun Γ name =>
                 name <- fresh_ty_arg_name (tvar_name name) Γ;;
                 ret (Γ ++ [name])%list) (ind_type_vars oib) [];;

       append "<";;
       append_join ", " ("'a" :: Γ);;
       append "> {";;

       (* Print constructors *)
       push_indent (col + indent_size);;
       append_nl_and_indent;;

       monad_append_join (append ",";; append_nl_and_indent)
                         (map (fun '(name, data) =>
                                 print_ind_ctor_definition Γ (kn.1, name) data)
                              (Ex.ind_ctors oib));;

       pop_indent;;
       append_nl_and_indent;;
       append "}";;

       print_ind_bodies l append_nl_and_indent ((ind_name, ind_ml_name) :: names)
     end) (Ex.ind_bodies mib) (ret tt) [];;
  pop_indent;;
  ret names.

Definition print_type_alias
           (nm : kername)
           (tvars : list type_var_info)
           (bt : box_type) : PrettyPrinter string :=
  let ty_ml_name := get_ty_name nm in
  append ("type " ++ ty_ml_name ++ "<");;
  Γrev <- monad_fold_left (fun Γ tvar => name <- fresh_ty_arg_name (tvar_name tvar) Γ;;
                                         ret (name :: Γ))
                          tvars [];;
  let Γ := rev Γrev in
  append_join ", " ("'a" :: Γ);;
  append "> = ";;
  print_type Γ bt;;
  append ";";;
  ret ty_ml_name.

Fixpoint print_decls_aux
         (decls : list (kername * bool * Ex.global_decl))
         (prefix : PrettyPrinter unit)
         (names : list (kername × string)) : PrettyPrinter (list (kername × string)) :=
  match decls with
  | [] => ret names
  | (kn, has_deps, decl) :: decls =>
    new_names <-
    (if has_deps then
       match decl with
       | Ex.ConstantDecl
           {| Ex.cst_type := type;
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
    print_decls_aux decls (append_nl;; append_nl_and_indent) (new_names ++ names)%list
  end.

Definition print_decls decls :=
  print_decls_aux decls (ret tt) [].

Definition preamble := [
"#![allow(dead_code)]";
"#![allow(non_camel_case_types)]";
"#![allow(unused_imports)]";
"#![allow(non_snake_case)]";
"#![allow(unused_variables)]";
"";
"use std::marker::PhantomData;";
"";
"fn hint_app<TArg, TRet>(f: &dyn Fn(TArg) -> TRet) -> &dyn Fn(TArg) -> TRet {";
"  f";
"}" ].

Definition program_preamble := [
"fn alloc<T>(&'a self, t: T) -> &'a T {";
"  self.__alloc.alloc(t)";
"}";
"";
"fn closure<TArg, TRet>(&'a self, F: impl Fn(TArg) -> TRet + 'a) -> &'a dyn Fn(TArg) -> TRet {";
"  self.__alloc.alloc(F)";
"}" ].

Definition print_program : PrettyPrinter (list (kername * string)) :=
  sig_col <- get_current_line_length;;
  push_indent sig_col;;

  monad_append_join append_nl_and_indent (map append preamble);;

  let is_const '(kn, decl) :=
      match decl with
      | Ex.ConstantDecl _ => true
      | _ => false
      end in
  ind_names <- print_decls_aux (filter (negb ∘ is_const) (List.rev Σ))
                               (append_nl;; append_nl_and_indent)
                               [];;

  (* First print a structure that has the arena and all
     (non-polymorphic) constants in the program *)
  let constants :=
      flat_map (fun '(kn, has_deps, decl) =>
                  match decl with
                  | Ex.ConstantDecl cst => [(kn, has_deps, cst)]
                  | _ => []
                  end) (List.rev Σ) in

  append_nl;;
  append_nl_and_indent;;
  push_indent (sig_col + indent_size);;

  append "struct Program<'a> {";;
  append_nl_and_indent;;
  append "__alloc: bumpalo::Bump,";;

  monad_fold_left (fun _ '(kn, has_deps, cst) =>
                     if is_polymorphic cst then
                       ret tt
                     else
                       append_nl_and_indent;;
                       append "__";;
                       append (get_const_name kn);;
                       append ": std::cell::Cell<std::option::Option<";;
                       print_type [] (Ex.cst_type cst).2;;
                       append ">>,") constants tt;;
  pop_indent;;
  append_nl_and_indent;;
  append "}";;

  (* Next we print all the code as associated members. First
     we print a way to create such a program. *)
  append_nl;;
  append_nl_and_indent;;
  append "impl<'a> Program<'a> {";;

  append_nl_and_indent;;
  append "fn new() -> Self {";;

  push_indent (sig_col + indent_size);;
  append_nl_and_indent;;
  append "Program {";;

  push_indent (sig_col + 2*indent_size);;
  append_nl_and_indent;;
  append "__alloc: bumpalo::Bump::new(),";;

  monad_fold_left (fun _ '(kn, has_deps, cst) =>
                     if is_polymorphic cst then
                       ret tt
                     else
                       append_nl_and_indent;;
                       append "__";;
                       append (get_const_name kn);;
                       append ": std::cell::Cell::new(None),") constants tt;;

  pop_indent;;
  append_nl_and_indent;;
  append "}";;

  pop_indent;;
  append_nl_and_indent;;
  append "}";;

  append_nl;;
  append_nl;;
  monad_append_join append_nl_and_indent (map append program_preamble);;

  (* Finally print all constants *)
  const_names <- print_decls_aux
                   (map (on_snd Ex.ConstantDecl) constants)
                   (append_nl;; append_nl_and_indent)
                   [];;

  append_nl_and_indent;;
  append "}";;

  pop_indent;;

  ret (const_names ++ ind_names)%list.
End FixEnv.

(*
Instance RustConfig : RustPrintConfig :=
  {| term_box_symbol := "()";
     type_box_symbol := "()";
     any_type_symbol := "()";
     print_full_names := false |}.

Definition general_extract (p : T.program) (ignore: list kername) (TT : list (kername * string)) : result string string :=
  entry <- match p.2 with
           | T.tConst kn _ => ret kn
           | T.tInd ind _ => ret (inductive_mind ind)
           | _ => Err "Expected program to be a tConst or tInd"
           end;;
  Σ <- extract_template_env
         extract_within_coq
         p.1
         (KernameSet.singleton entry)
         (fun k => existsb (eq_kername k) ignore);;
  let Σ := opt_top_level_fixes Σ in
  let TT_fun kn := option_map snd (List.find (fun '(kn',v) => eq_kername kn kn') TT) in
  let p :=
      names <- print_program Σ TT_fun;;
      append_nl;;
      append "fn main() {";;
      append_nl;;
      let name := get_const_name TT_fun entry in
      append ("  print!(""{:?}"", Program::new()." ++ name ++ "())");;
      append_nl;;
      append "}" in
  '(_, s) <- finish_print p;;
  ret s.

Definition extract (p : T.program) : result string string :=
  general_extract p [] [].

Open Scope nat.
Fixpoint ack (n m : nat) : nat :=
  match n with
  | O => S m
  | S p => let fix ackn (m : nat) :=
               match m with
               | O => ack p 1
               | S q => ack p (ackn q)
               end
           in let v := ackn m in v
  end.
Definition code := ack 3 4.
MetaCoq Quote Recursively Definition ex := code.
Definition printed := Eval vm_compute in extract ex.
MetaCoq Run (match printed with
             | Ok s => tmMsg s
             | Err s => tmFail s
             end).

*)

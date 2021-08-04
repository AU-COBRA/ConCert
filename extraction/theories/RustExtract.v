From ConCert.Execution Require Import Blockchain.
From ConCert.Execution Require Import Serializable.
From ConCert.Execution Require Import Containers.
From ConCert.Extraction Require Import Common.
From ConCert.Extraction Require Import Erasure.
From ConCert.Extraction Require Import ExAst.
From ConCert.Extraction Require Import ExpandBranches.
From ConCert.Extraction Require Import Extraction.
From ConCert.Extraction Require Import CertifyingInlining.
From ConCert.Extraction Require Import Optimize.
From ConCert.Extraction Require Import PrettyPrinterMonad.
From ConCert.Extraction Require Import Printing.
From ConCert.Extraction Require Import ResultMonad.
From ConCert.Extraction Require Import TopLevelFixes.
From ConCert.Extraction Require Import Utils.
From ConCert.Utils Require Import StringExtra.

From Coq Require Import Arith.
From Coq Require Import Ascii.
From Coq Require Import List.
From Coq Require Import NArith.
From Coq Require Import PArith.
From Coq Require Import String.
From Coq Require Import ZArith.

From MetaCoq.SafeChecker Require Import PCUICSafeChecker SafeTemplateChecker.
From MetaCoq.Template Require Import Kernames All.
From MetaCoq.Erasure Require Import Loader EAst EAstUtils ELiftSubst ETyping.

Import StringExtra.
Import String.
Import PrettyPrinterMonad.

Module P := MetaCoq.PCUIC.PCUICAst.
Module PT := MetaCoq.PCUIC.PCUICTyping.
Module T2P := MetaCoq.PCUIC.TemplateToPCUIC.
Module E := MetaCoq.Erasure.EAst.
Module T := MetaCoq.Template.Ast.
Module TUtil := MetaCoq.Template.AstUtils.
Module EF := MetaCoq.Erasure.ErasureFunction.
Module Ex := ConCert.Extraction.ExAst.

Import PrettyPrinterMonad.
Import ListNotations.
Import MonadNotation.

Local Open Scope list.
Local Open Scope string.

Local Definition indent_size := 2.

Section FixEnv.
Context (Σ : Ex.global_env).
Context (remaps : remaps).
(* A printing config for Rust *)
Class RustPrintConfig :=
  { term_box_symbol : string;
    type_box_symbol : string;
    any_type_symbol : string;
    print_full_names : bool (* use fully-qualified names as identifiers to avoid name clashes *)}.

Context `{RustPrintConfig}.

Definition ind_attr_map := inductive -> string.

Context (ind_attrs : ind_attr_map).

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

(* We clean global identifiers but do not generate any form of fresh names
   to make it straightforward to know what extracted code maps to what. *)
Definition clean_global_ident (s : string) : string :=
  replace_char "." "_" (replace_char "'" "_" s).

(* Get identifier for a global constant function given its kername, without
   taking remappings into account *)
Definition const_global_ident_of_kername (kn : kername) :=
  clean_global_ident (if print_full_names then string_of_kername kn else kn.2).

(* Get identifier for a global constant meant to be used as a type, without
   taking remappings into account. This is also used for [inductive]. *)
Definition ty_const_global_ident_of_kername (kn : kername) :=
  capitalize (clean_global_ident (if print_full_names then string_of_kername kn else kn.2)).

(* Get identifier for a global type alias taking remappings into account *)
Definition get_ty_const_ident (name : kername) : string :=
  match remap_inline_constant remaps name with
  | Some s => s
  | None => ty_const_global_ident_of_kername name
  end.

(* Get identifier for an inductive taking remappings into account *)
Definition get_ind_ident (ind : inductive) : PrettyPrinter string :=
  match remap_inductive remaps ind with
  | Some rem => ret (re_ind_name rem)
  | None =>
    oib <- wrap_result (lookup_ind_decl ind) id;;
    let kn := ((inductive_mind ind).1, Ex.ind_name oib) in
    ret (ty_const_global_ident_of_kername kn)
  end.

(* Fine to remove primes here as we generate fresh names *)
Definition clean_local_ident (name : ident) : string :=
  remove_char "'" name.

Definition is_polymorphic (cst : Ex.constant_body) : bool :=
  0 <? #|(Ex.cst_type cst).1|.

Definition print_ind (ind : inductive) : PrettyPrinter unit :=
  get_ind_ident ind >>= append.

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
  | nNamed name => ret (fresh (clean_local_ident name) (Γ ++ used_names))
  end.

Definition fresh_ty_arg_name (name : name) (Γ : list ident) : PrettyPrinter ident :=
  used_names <- get_used_names;;
  match name with
  | nAnon => ret (fresh "a" (Γ ++ used_names))
  | nNamed name => ret (fresh (clean_local_ident name) (Γ ++ used_names))
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
    if remap_inductive remaps ind then
      print_ind ind;;
      print_parenthesized_with
        "<" ">"
        (0 <? #|args|)
        (monad_append_join (append ", ") args)
    else
      append "&'a ";;
      print_ind ind;;
      append "<";;
      monad_append_join (append ", ") (append "'a" :: args);;
      append ">"

  | TConst name =>
    append (get_ty_const_ident name ++ "<");;
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

Definition print_app
           (head : PrettyPrinter unit)
           (args : list (PrettyPrinter unit)) : PrettyPrinter unit :=
  col <- get_current_line_length;;
  head;;
  push_indent (col + indent_size);;
  append "(";;
  (if 0 <? #|args| then append_nl else ret tt);;
  monad_append_join (append ",";; append_nl) args;;
  append ")";;
  pop_indent.

Definition print_constructor
           (ind : inductive)
           (c : nat)
           (args : list (PrettyPrinter unit)) :=
  match remap_inductive remaps ind with
  | Some rem =>
    s <- wrap_option (nth_error (re_ind_ctors rem) c)
                     (string_of_inductive ind
                      ^ "' does not remap enough constructors ");;
    if 0 <? #|args| then
      print_app (append s) args
    else
      append s
  | None =>
    oib <- wrap_result (lookup_ind_decl ind) id;;
    '(ctor, _) <- wrap_option
                    (nth_error (Ex.ind_ctors oib) c)
                    ("Could not find ctor "
                     ^ string_of_nat c
                     ^ " for inductive "
                     ^ string_of_inductive ind);;

    col <- get_current_line_length;;
    push_indent (col + indent_size);;
    append "self.alloc(";;
    append_nl;;
    let head := print_ind ind;; append "::";; append (clean_global_ident ctor) in
    let final_args := append "PhantomData" :: args in
    print_app head final_args;;
    append ")";;
    pop_indent
  end.

Definition print_const (kn : kername) (args : list (PrettyPrinter unit)) : PrettyPrinter unit :=
  num_inline_args <- get_num_inline_args kn;;
  let (expr, num_inline_args) :=
      if #|args| <? num_inline_args then
        (* Not enough args, use curried version *)
        ("self." ^ const_global_ident_of_kername kn ^ "__curried", 0)
      else
        (match remap_inline_constant remaps kn with
         | Some s => s
         | None => "self." ^ const_global_ident_of_kername kn
         end, num_inline_args) in
  head_col <- get_current_line_length;;
  let head := append expr in
  let args_in_head := firstn num_inline_args args in
  let args_in_tail := skipn num_inline_args args in
  print_app head args_in_head;;
  push_indent (head_col + indent_size);;
  let it_app a :=
      append "(";;
      append_nl;;
      a;;
      append ")" in
  monad_append_concat (map it_app args_in_tail);;
  pop_indent.

Section print_term.
  Context (print_term : list ident -> term -> PrettyPrinter unit).

  Definition print_case Γ ind npars discr brs : PrettyPrinter unit :=
    col <- get_current_line_length;;
    push_indent col;;

    append "match ";;
    print_term Γ discr;;
    append " {";;

    oib <- wrap_result (lookup_ind_decl ind) id;;
    let rem := remap_inductive remaps ind in

    push_indent (col + indent_size);;
    (fix print_cases
         (brs : list (nat × term))
         (ctors : list (ident × list (name × box_type)))
         (c : nat) :=
       match brs, ctors with
       | [], [] => ret tt
       | (arity, t) :: branches, (ctor_name, data) :: ctors =>
         append_nl;;

         match rem with
         | Some rem =>
           s <- wrap_option (nth_error (re_ind_ctors rem) c)
                            (string_of_inductive ind
                             ^ "' does not remap enough constructors");;
           append s

         | None =>
           append "&";;
           print_ind ind;;
           append "::";;
           append (clean_global_ident ctor_name)
         end;;

         push_indent (col + 2*indent_size);;
         (fix print_branch (n : nat) (Γ : list ident) (t : term) {struct t} :=
            match n, t with
            | 0, _ =>
              (* In Coq, parameters are not part of branches. But
            erasure adds the parameters to each constructor, so we
            need to get those out of the way first. These won't have
            any uses so we just print _. In addition, we add a phantom
            data when not remapped to make it valid to always have
            lifetimes. That gives another underscores. *)
              let nextra := if rem then npars else S npars in
              let extra := List.repeat "_" nextra in
              let args := (extra ++ rev (firstn arity Γ))%list in
              print_parenthesized (0 <? #|args|) (append_join ", " args);;
              append " => {";;
              append_nl;;
              print_term Γ t

            | S n, tLambda name t =>
              name <- fresh_ident name Γ;;
              print_branch n (name :: Γ) t
            | _, _ => printer_fail "Could not decompose case branch"
            end) arity Γ t;;

         pop_indent;;
         append_nl;;
         append "},";;

         print_cases branches ctors (S c)
       | _, _ => printer_fail "wrong number of case branches compared to inductive"
       end) brs (Ex.ind_ctors oib) 0;;

    pop_indent;;
    append_nl;;
    append "}";;

    pop_indent.

  Definition print_remapped_case Γ ind discr brs eliminator : PrettyPrinter unit :=
    col <- get_current_line_length;;
    push_indent col;;

    append (eliminator ^ "(");;

    oib <- wrap_result (lookup_ind_decl ind) id;;

    push_indent (col + indent_size);;

    let fix print_branch (arity n : nat) (Γ : list ident) (t : term) {struct t} :=
        match n, t with
        | 0, _ =>
          let args := rev (firstn arity Γ) in

          append_nl;;
          append_concat (map (fun a => a ^ ", ") args);;
          append "{";;

          push_indent (col + 2*indent_size);;
          append_nl;;
          print_term Γ t;;
          pop_indent;;

          append_nl;;
          append "},"

        | S n, tLambda name t =>
          name <- fresh_ident name Γ;;
          print_branch arity n (name :: Γ) t
        | _, _ => printer_fail "Could not decompose case branch"
        end in
    monad_append_concat
      (map (fun '(ar, t) => print_branch ar ar Γ t) brs);;

    append_nl;;
    print_term Γ discr;;

    append ")";;
    pop_indent;;
    pop_indent.
End print_term.

Definition needs_block (t : term) : bool :=
  match t with
  | tLetIn _ _ _
  | tFix _ _ => true
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
    append_nl;;
    let Γ := name :: Γ in
    print_term Γ t;;
    pop_indent;;
    append_nl;;
    append "})";;
    pop_indent

  | tLetIn na val body =>
    name <- fresh_ident na Γ;;
    col <- get_current_line_length;;

    push_indent col;;
    append ("let " ++ name ++ " =");;
    (if needs_block val then append " {" else ret tt);;

    push_indent (col + indent_size);;
    append_nl;;
    print_term Γ val;;
    pop_indent;;

    (if needs_block val then
       append_nl;;
       append "};"
     else
       append ";");;

    append_nl;;

    print_term (name :: Γ) body;;
    pop_indent

  | tApp head arg =>

    (fix f head args_printed {struct head} :=
       match head with
       | tApp head arg =>
         let printed_arg :=
             (if needs_block arg then append "{ " else ret tt);;
             print_term Γ arg;;
             if needs_block arg then append " }" else ret tt in
         f head (printed_arg :: args_printed)

       | tConstruct ind i => print_constructor ind i args_printed

       | tConst kn => print_const kn args_printed

       | _ =>
         (* For other heads we might need to guide type inference by repeatedly
            applying a hint function *)
         append (concat "" (repeat "hint_app(" #|args_printed|));;
         (if needs_block head then append "{ " else ret tt);;
         print_term Γ head;;
         (if needs_block head then append " }" else ret tt);;
         append ")";;
         monad_fold_left
           (fun pref a => append pref;; a;; append ")";; ret ")(") args_printed "(";;
         ret tt

       end) head [if needs_block arg then
                    append "{ ";; print_term Γ arg;; append " }"
                  else
                    print_term Γ arg]

  | tConst kn => print_const kn []
  | tConstruct ind i => print_constructor ind i []

  | tCase (ind, npars) discr brs =>
    match brs with
    | [] =>
      (* If it's a match on an empty type, we just panic, since we should never reach this code *)
      append "panic!(""Absurd case!"")"
    | _ =>
      match remap_inductive remaps ind with
      | Some rem =>
        match re_ind_match rem with
        | Some s => print_remapped_case print_term Γ ind discr brs s
        | None => print_case print_term Γ ind npars discr brs
        end
      | None => print_case print_term Γ ind npars discr brs
      end
    end
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
            append_nl;;
            ret ((na ++ ".get().unwrap()") :: Γ, na :: cells))
         defs (Γ, []);;

    let cells := rev cells in

    (* Print closures. *)
    monad_fold_left
      (fun _ '(print_def, cell) =>
         append (cell ++ ".set(Some(");;
         push_indent (col + indent_size);;
         append_nl;;
         print_def;;
         append "));";;
         pop_indent;;
         append_nl)
      (combine
         (map (fun d => print_term Γ (dbody d)) defs)
         cells)
      tt;;

    append (nth i cells "" ++ ".get().unwrap()");;
    pop_indent

  | tProj ((ind, pars), c) t =>
    printer_fail ("unhandled tProj on " ^ string_of_kername (inductive_mind ind))

  | tCoFix _ _ => printer_fail "Cannot handle tCoFix yet"
  | tPrim _ => printer_fail "Cannot handle Coq primitive types yet"
  end.

Definition print_constant
           (kn : kername)
           (type : (list name × box_type))
           (body : E.term) : PrettyPrinter unit :=

  let rname := const_global_ident_of_kername kn in

  name_col <- get_current_line_length;;
  push_indent name_col;;

  let (type_vars, ty) := type in
  Γty <- monad_fold_left (fun Γty name => name <- fresh_ty_arg_name name Γty;;
                                          ret (Γty ++ [name])%list)
                         type_vars [];;

  (* Print version with inlined args *)
  match remap_constant remaps kn with
  | Some s => append (StringExtra.replace "##name##" rname s)
  | None =>
    if remap_inline_constant remaps kn then
      ret tt
    else
      append ("fn " ++ rname);;
      print_parenthesized_with
        "<" ">" (0 <? #|Γty|)
        (append_join ", " (map (fun na => na ++ ": Copy") Γty));;
      append "(&'a self";;

      (fix print_top Γ body ty :=
         match body, ty with
         | tLambda na body, TArr dom cod =>
           na <- fresh_ident na Γ;;
           append (", " ++ na ++ ": ");;
           print_type Γty dom;;
           print_top (na :: Γ) body cod
         | _, _ =>
           append ") -> ";;
           print_type Γty ty;;
           append " {";;

           push_indent (name_col + indent_size);;
           append_nl;;

           push_use rname;;
           print_term Γ body;;

           pop_indent;;
           append_nl;;
           append "}"
         end) [] body ty
  end;;

  (* Print curried version if there were inlined args *)
  num_inline_args <- get_num_inline_args kn;;
  (if 0 <? num_inline_args then
     append_nl;;
     append ("fn " ++ rname ++ "__curried");;
     print_parenthesized_with
       "<" ">" (0 <? #|Γty|)
       (append_join ", " (map (fun na => na ++ ": Copy") Γty));;
     append "(&'a self) -> ";;
     print_type Γty ty;;
     append " {";;

     push_indent (name_col + indent_size);;
     append_nl;;

     push_use (rname ++ "__curried");;
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
     append_nl;;
     append "}"
   else
     ret tt);;

  pop_indent;;
  ret tt.

Definition print_ind_ctor_definition
           (Γ : list ident)
           (ctor_name : ident)
           (data : list (name × box_type)) : PrettyPrinter unit :=
  append (clean_global_ident ctor_name);;

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
  let print_datas := print_phantom :: map (print_type Γ ∘ snd) data in
  monad_append_join (append ", ") print_datas;;

  append ")".

Local Open Scope string.
Definition print_mutual_inductive_body
           (kn : kername)
           (mib : Ex.mutual_inductive_body) : PrettyPrinter unit :=
  col <- get_current_line_length;;
  push_indent col;;

  names <-
  (fix print_ind_bodies
       (l : list Ex.one_inductive_body)
       (prefix : PrettyPrinter unit)
       (i : nat) :=
     match l with
     | [] => ret tt
     | oib :: l =>

       prefix;;

       append (ind_attrs (mkInd kn i));;
       append_nl;;
       append "pub enum ";;
       print_ind (mkInd kn i);;

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
       append_nl;;

       monad_append_join (append ",";; append_nl)
                         (map (fun '(name, data) =>
                                 print_ind_ctor_definition Γ name data)
                              (Ex.ind_ctors oib));;

       pop_indent;;
       append_nl;;
       append "}";;

       print_ind_bodies l append_nl (S i)
     end) (Ex.ind_bodies mib) (ret tt) 0;;
  pop_indent;;
  ret names.

Definition print_type_alias
           (nm : kername)
           (tvars : list type_var_info)
           (bt : box_type) : PrettyPrinter unit :=
  let rname := ty_const_global_ident_of_kername nm in
  match remap_constant remaps nm with
  | Some s => append (StringExtra.replace "##name##" rname s)
  | None =>
    append ("type " ++ rname ++ "<");;
    Γrev <- monad_fold_left (fun Γ tvar => name <- fresh_ty_arg_name (tvar_name tvar) Γ;;
                                           ret (name :: Γ))
                          tvars [];;
    let Γ := rev Γrev in
    append_join ", " ("'a" :: Γ);;
    append "> = ";;
    print_type Γ bt;;
    append ";"
  end.

Fixpoint print_decls_aux
         (decls : list (kername * bool * Ex.global_decl))
         (prefix : PrettyPrinter unit) : PrettyPrinter unit :=
  match decls with
  | [] => ret tt
  | (kn, has_deps, decl) :: decls =>
    match decl with
    | Ex.ConstantDecl {| Ex.cst_type := type; Ex.cst_body := Some body |} =>
      prefix;; print_constant kn type body
    | Ex.InductiveDecl mib =>
      if remap_inductive remaps (mkInd kn 0) then
        ret tt
      else
        prefix;; print_mutual_inductive_body kn mib
    | Ex.TypeAliasDecl (Some (tvars, bt)) => prefix;; print_type_alias kn tvars bt
    | _ => ret tt
    end;;
    print_decls_aux decls (append_nl;; append_nl)
  end.

Definition print_decls decls :=
  print_decls_aux decls (ret tt).

Class Preamble :=
  { top_preamble : list string;
    program_preamble : list string }.

Context `{Preamble}.

Definition print_program : PrettyPrinter unit :=
  sig_col <- get_current_line_length;;
  push_indent sig_col;;

  monad_append_join append_nl (map append top_preamble);;

  let is_const '(kn, decl) :=
      match decl with
      | Ex.ConstantDecl _ => true
      | _ => false
      end in

  (* Filtering out empty type declarations *)
  (* TODO: possibly, move to extraction (requires modifications of the correctness proof) *)
  let Σ := filter (fun '(kn,d) => negb (is_empty_type_decl d)) Σ in

  ind_names <- print_decls_aux (filter (negb ∘ is_const) (List.rev Σ))
                               (append_nl;; append_nl);;

  (* First print a structure that has the arena and all
     (non-polymorphic) constants in the program *)
  let constants :=
      flat_map (fun '(kn, has_deps, decl) =>
                  match decl with
                  | Ex.ConstantDecl cst => [(kn, has_deps, cst)]
                  | _ => []
                  end) (List.rev Σ) in

  append_nl;;
  append_nl;;
  push_indent (sig_col + indent_size);;

  append "struct Program {";;
  append_nl;;
  append "__alloc: bumpalo::Bump,";;

  pop_indent;;
  append_nl;;
  append "}";;

  (* Next we print all the code as associated members. First
     we print a way to create such a program. *)
  append_nl;;
  append_nl;;
  append "impl<'a> Program {";;

  append_nl;;
  append "fn new() -> Self {";;

  push_indent (sig_col + indent_size);;
  append_nl;;
  append "Program {";;

  push_indent (sig_col + 2*indent_size);;
  append_nl;;
  append "__alloc: bumpalo::Bump::new(),";;

  pop_indent;;
  append_nl;;
  append "}";;

  pop_indent;;
  append_nl;;
  append "}";;

  append_nl;;
  append_nl;;
  monad_append_join append_nl (map append program_preamble);;

  (* Finally print all constants *)
  const_names <- print_decls_aux
                   (map (on_snd Ex.ConstantDecl) constants)
                   (append_nl;; append_nl);;

  append_nl;;
  append "}";;

  pop_indent.
End FixEnv.

Definition extract_rust_within_coq
           (overridden_masks : kername -> option bitmask)
           (should_inline : kername -> bool) : extract_template_env_params :=
  {| check_wf_env_func := check_wf_env_func extract_within_coq;
     template_transforms := [template_inline should_inline];
     pcuic_args :=
       {| optimize_prop_discr := true;
          extract_transforms := [dearg_transform overridden_masks true false false false false;
                                 ExpandBranches.transform;
                                 TopLevelFixes.transform] |} |}.

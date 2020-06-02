From ConCert.Execution Require Import Blockchain.
From ConCert.Execution Require Import Serializable.
From ConCert.Execution Require Import Containers.
From ConCert.Extraction Require Import Certified.
From ConCert.Extraction Require Import Common.
From ConCert.Extraction Require Import Erasure.
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
Module TL := MetaCoq.Template.Typing.TemplateLookup.
Module TUtil := MetaCoq.Template.AstUtils.
Module EF := MetaCoq.Erasure.SafeErasureFunction.
Module Ex := ConCert.Extraction.Erasure.EAst.

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

Bind Scope string with kername ident.

Definition option_get {A} (o : option A) (default : A) : A :=
  match o with
  | Some a => a
  | None => default
  end.

Definition get_fun_name (name : kername) : string :=
  option_get
    (translate name)
    (uncapitalize (replace_char "." "_" (kername_unqual name))).
    (*(uncapitalize (replace_char "." "_" name)).*)

Definition get_ty_name (name : kername) : string :=
  option_get
    (translate name)
    (capitalize (replace_char "." "_" (kername_unqual name))).

Definition get_ctor_name (name : kername) : string :=
  option_get
    (translate name)
    ((*capitalize (replace "." "_" name) really long names, but no collisions *)
     capitalize (kername_unqual name)).

Definition get_ident_name (name : ident) : string :=
  uncapitalize (remove_char "'" (replace_char "." "_" name)).

Definition get_ty_arg_name (name : ident) : ident :=
  uncapitalize name.

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
                     ++ " in mutual inductive " ++ inductive_mind ind)
    end
  | _ => Err ("Could not find inductive " ++ inductive_mind ind ++ " in environment")
  end.

Definition names_lookup_ind_decl (ind : inductive) : option T.one_inductive_body :=
  match TL.lookup_env Σnames (inductive_mind ind) with
  | Some (T.InductiveDecl {| T.ind_bodies := oibs |}) =>
    nth_error oibs (inductive_ind ind)
  | _ => None
  end.

Definition print_ind (ind : inductive) : PrettyPrinter unit :=
  match lookup_ind_decl ind with
  | Ok oib =>
    let qual := kername_qualifier (inductive_mind ind) in
    let kername := qual ++ "." ++ Ex.ind_name oib in
    append (get_ty_name kername)
  | Err err =>
    (* Not found in extraction environment, lookup in names environment *)
    match names_lookup_ind_decl ind with
    | Some oib =>
      let qual := kername_qualifier (inductive_mind ind) in
      let kername := qual ++ "." ++ T.ind_name oib in
      (* We require this to be translated now *)
      append =<< wrap_option (translate kername) ("No translation for " ++ kername)
    | None => printer_fail err
    end
  end.

Definition print_ind_ctor (ind : inductive) (i : nat) : PrettyPrinter unit :=
  match lookup_ind_decl ind with
  | Ok oib =>
    match nth_error (Ex.ind_ctors oib) i with
    | Some (name, _) =>
      let qual := kername_qualifier (inductive_mind ind) in
      let kername := qual ++ "." ++ name in
      append (get_ctor_name kername)
    | None =>
      printer_fail (Ex.ind_name oib ++ " does not have a ctor " ++ string_of_nat i)
    end
  | Err err =>
    match names_lookup_ind_decl ind with
    | Some oib =>
      match nth_error (T.ind_ctors oib) i with
      | Some (name, _, _) =>
        let qual := kername_qualifier (inductive_mind ind) in
        let kername := qual ++ "." ++ name in
        append =<< wrap_option (translate kername) ("No translation for " ++ kername)
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
  | nAnon => ret (fresh "anon" (Γ ++ used_names))
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
  | TBox => append "□"
  | TAny => append "𝕋"
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
  | tBox _ => append "□"
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

  | tCase (ind, _) discriminee branches =>
    case_col <- get_current_line_length;;
    append "case ";;
    print_parenthesized (parenthesize_case_discriminee discriminee)
                        (print_term Γ discriminee);;
    append " of";;

    push_indent (case_col + indent_size);;

    oib <- wrap_result (lookup_ind_decl ind) id;;

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

  match type with
  | (type_vars, ty) =>
    append ml_name;;
    append " : ";;
    Γrev <- monad_fold_left (fun Γ name => name <- fresh_ty_arg_name name Γ;;
                                           ret (name :: Γ))
                            type_vars [];;
    print_type (rev Γrev) ty;;
    append_nl_and_indent
  (*| Err s =>
    append ("-- Could not erase type: " ++ s);;
    append_nl_and_indent*)
  end;;

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
  | TBox
  | TAny
  | TVar _
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
       let ind_name := qualifier ++ "." ++ ind_name oib in
       let ind_ml_name := get_ty_name ind_name in
       append ind_ml_name;;

       (* Print type args *)
       monad_fold_left (fun _ name => append (" " ++ name)) Γ tt;;

       push_indent (col + indent_size);;

       (fix print_ind_ctors (ctors : list (ident * list box_type)) prefix :=
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

  names <- (fix f l prefix names :=
     match l with
     | [] => ret names
     | (name, decl) :: l =>

       prefix;;
       new_names <- print_global_decl name decl;;

       f l (append_nl;; append_nl_and_indent) (new_names ++ names)%list
     end) (List.rev Σ) (ret tt) [];;

  pop_indent;;

  ret names.
End FixEnv.

From Coq Require VectorDef.
Section Counter.
Context `{ChainBase}.
Inductive Msg :=
| increment
| decrement.

Global Instance Serializable_Msg : Serializable Msg :=
  Derive Serializable Msg_rect<increment, decrement>.

Import VectorDef VectorNotations.
Fixpoint sum_vec {n : nat} (v : Vector.t Z n) : Z :=
  match v with
  | [] => 0
  | z :: v => z + sum_vec v
  end.

Fixpoint seq_vec (start : Z) (count : nat) : Vector.t Z count :=
  match count with
  | 0 => []
  | S count => start :: seq_vec (start + 1) count
  end.

Local Open Scope Z.
Program Definition init
           (chain : Chain)
           (ctx : ContractCallContext)
           (setup : unit) : option Z :=
  Some (sum_vec (seq_vec 17 7)).

Open Scope list.
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

Notation "'eval_extract' x" :=
  ltac:(let x :=
            eval
              cbv
              beta
              delta [x receive RecordSet.set RecordSet.constructor Monads.bind Monads.option_monad]
              iota in x in
       exact x) (at level 70).

(*From ConCert.Execution Require Import Escrow.

Definition escrow_init :=
  eval_extract @Escrow.init.

Definition escrow_receive :=
  eval_extract @Escrow.receive.

Quote Recursively Definition program := (escrow_init, escrow_receive).
Definition init_name := "ConCert.Extraction.MidlangExtract.escrow_init".
Definition receive_name := "ConCert.Extraction.MidlangExtract.escrow_receive".*)

Quote Recursively Definition program := (init, receive).
Definition init_name := "ConCert.Extraction.MidlangExtract.init".
Definition receive_name := "ConCert.Extraction.MidlangExtract.receive".

Definition midlang_translation_map :=
  [("ConCert.Execution.Blockchain.current_slot", "current_slot");
   ("ConCert.Execution.Blockchain.account_balance", "account_balance");
   ("ConCert.Execution.Blockchain.address_eqb", "address_eq");
   ("ConCert.Execution.Blockchain.ctx_amount", "amount");
   ("ConCert.Execution.Blockchain.ctx_from", "from");
   ("ConCert.Execution.Blockchain.Chain", "ConCertChain");
   ("ConCert.Execution.Blockchain.ContractCallContext", "ConCertCallContext");
   ("ConCert.Execution.Blockchain.ActionBody", "ConCertAction");
   ("ConCert.Execution.Blockchain.ChainBase", "ChainBaseWTF");
   ("ConCert.Execution.Blockchain.act_transfer", "transfer");
   ("ConCert.Execution.Blockchain.ctx_contract_address", "contract_address")].
Definition midlang_translate (name : kername) : option string :=
  match find (fun '(key, _) => key =? name) midlang_translation_map with
  | Some (_, val) => Some val
  | None => None
  end.

Definition extra_ignored :=
  ["RecordUpdate.RecordSet.Reader";
   "RecordUpdate.RecordSet.constructor"].

Definition test :=
    specialize_erase_debox_template_env
      (List.rev program.1)
      [init_name; receive_name]
      (ignored_concert_types ++ extra_ignored ++ map fst midlang_translation_map).
Time Compute
     (env <- test;;
      '(_, s) <- finish_print (print_env env program.1 midlang_translate);;
      ret s).

(*From ConCert.Execution Require Import Escrow.*)

Axiom extraction_chain_base : ChainBase.
Existing Instance extraction_chain_base.
Definition foo : TemplateMonad unit :=
  s <- get_contract_extraction_set contract;;
  tmPrint s;;
  @tmFail unit "done";;
  result <- tmEval lazy (finish_print (print_env (env s)));;
  match result with
  | Ok (name_map, result) => tmMsg result
  | Err s => tmFail s
  end.

Fail Run TemplateProgram foo.

Recursive Extraction test_eq_dec.

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
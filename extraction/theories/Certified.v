From Coq Require Import PeanoNat ZArith.

From MetaCoq.Template Require Import Loader.
From MetaCoq.Erasure Require Import SafeTemplateErasure Debox.
From MetaCoq.Erasure Require ErasureFunction.
From MetaCoq.Erasure Require SafeErasureFunction.
From MetaCoq.Template Require Import config.
From MetaCoq.SafeChecker Require Import PCUICSafeReduce PCUICSafeChecker
     SafeTemplateChecker.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICTyping
     TemplateToPCUIC.

From MetaCoq.Template Require Pretty.

From ConCert Require Import MyEnv.
From ConCert.Embedding Require Import Notations.
From ConCert.Embedding Require Import SimpleBlockchain.
From ConCert.Extraction Require Import LPretty.
From ConCert.Extraction Require Import Counter.

From Coq Require Import List Ascii String.
Local Open Scope string_scope.

From MetaCoq.Template Require Import All.

Import ListNotations.
Import AcornBlockchain.
Import MonadNotation.

(** Taken from [SafeTemplateErasure] and modified
    This uses the retyping-based erasure *)
Program Definition erase_and_print_template_program {cf : checker_flags}
        (TT : env string)
        (afrer_erase : EAst.term -> EAst.term)
        (p : Ast.program)
  : string + string :=
  let p := fix_program_universes p in
  match erase_template_program p return string + string with
  | CorrectDecl (Σ', t) =>
    inl (LPretty.print_term Σ' [] TT [] true false (afrer_erase t))
  | EnvError Σ' (AlreadyDeclared id) =>
    inr ("Already declared: " ++ id)
  | EnvError Σ' (IllFormedDecl id e) =>
    inr ("Type error: " ++ PCUICSafeChecker.string_of_type_error Σ' e ++ ", while checking " ++ id)
  end.

Definition print_EnvCheck {A}
           (f : E.global_context -> A -> string)
           (checked_t : EnvCheck (E.global_context * A))
  : string + string :=
  match checked_t return string + string with
  | CorrectDecl (Σ', t) =>
    inl (f Σ' t)
  | EnvError Σ' (AlreadyDeclared id) =>
    inr ("Already declared: " ++ id)
  | EnvError Σ' (IllFormedDecl id e) =>
    inr ("Type error: " ++ PCUICSafeChecker.string_of_type_error Σ' e ++ ", while checking " ++ id)
  end.

Definition print_template_program (TT : env string)
           (checked_t : EnvCheck (EAst.global_context × EAst.term))
  : string + string :=
  print_EnvCheck (fun Σ t => LPretty.print_term Σ [] TT [] true false t) checked_t.

Program Definition check_applied
        (Σ : P.global_env)
        (et : E.term)
        (wf : ∥PCUICTyping.wf Σ∥) : EnvCheck bool :=
  is_const_applied <- wrap_error (P.empty_ext Σ) "during checking applied constant"
                                 (check_consts_applied (P.empty_ext Σ) _ [] et) ;;
  let is_constr_applied := check_ctors_applied Σ [] et in
  ret (Monad:=envcheck_monad) (andb is_const_applied is_constr_applied).
Next Obligation.
  destruct wf as [wf].
  constructor.
  split; [assumption| ].
  todo "on_udecl on empty universe context".
Qed.

Definition erase_and_check_applied (p : Ast.program) : EnvCheck bool :=
  let p := fix_program_universes p in
  let Σ := List.rev (trans_global (Ast.empty_ext p.1)).1 in
  G <- check_wf_env_only_univs Σ ;;
  et <- erase_template_program p ;;
  check_applied Σ et.2 (proj2 (projT2 G)).

Definition print_sum (s : string + string) :=
  match s with
  | inl s' => s'
  | inr s' => s'
  end.

Definition erase_print (TT : env string) (p : Ast.program) : string :=
  let p := fix_program_universes p in
  let checked_t := erase_template_program p in
  print_sum (print_template_program TT checked_t).

Definition liftM {M : Type -> Type} `{Monad M} {A B : Type}
           (f : A -> B) : M A -> M B :=
  fun ma => ma >>= ret ∘ f.

Definition erase_debox_types (TT : env string) (p : Ast.program) :
  EnvCheck (EAst.global_context × EAst.term) :=
  let p := fix_program_universes p in
  '(Σ,t) <- erase_template_program p ;;
  ret (Σ, debox_types [] t).

Definition erase_debox_all_applied (TT : env string) (p : Ast.program) :
  EnvCheck (EAst.global_context × EAst.term) :=
  let p := fix_program_universes p in
  '(Σ,t) <- erase_template_program p ;;
  ret (Σ, debox_all t).

Definition erase_print_deboxed (TT : env string) (p : Ast.program) : string :=
  let p := fix_program_universes p in
  let deboxed := erase_debox_types TT p in
  print_sum (print_template_program TT deboxed).

Definition erase_print_deboxed_all_applied (TT : env string) (p : Ast.program) : string :=
  let p := fix_program_universes p in
  let deboxed := erase_debox_all_applied TT p in
  print_sum (print_template_program TT deboxed).


Program Definition erase_check_debox_all (TT : env string) (p : Ast.program)
 : EnvCheck (EAst.global_context × (list E.aname * E.term))  :=
  let p := fix_program_universes p in
  let res : EnvCheck ((EAst.global_context × bool) × EAst.term):=
      '(Σ,t) <- erase_template_program p ;;
      is_ok <- erase_and_check_applied p ;;
      ret (Monad:=envcheck_monad) (Σ,is_ok,t)
  in
  match res with
  | CorrectDecl g =>
    let '(Σ,is_ok, t) := g in
    if is_ok : bool then
      let deboxed := debox_top_level (debox_all t) in
      CorrectDecl (Σ, Edecompose_lam deboxed)
    else
      let err_msg := "Not all constructors or constants are appropriately applied" in
      EnvError (P.empty_ext [])
                  (IllFormedDecl err_msg (Msg err_msg))
  | EnvError Σ' err => EnvError Σ' err
  end.


Definition print_decl (decl_name : string) (TT : env string) (tys : list Ast.term)
           (Σ : E.global_context) (decl_body : list E.aname * E.term) : string :=
  let (args,body) := decl_body in
  (* FIXME: this will produce wrong type annotations if the logical argument
     appears between the normal arguments! We need to switch to erased types and filter  out the boxes in types *)
  let targs := combine args tys in
  let printed_targs :=
      map (fun '(x,ty) => parens false (string_of_name x.(E.binder_name) ++ " : " ++ print_liq_type TT ty)) targs in
  let decl := decl_name ++ " " ++ concat " " printed_targs in
  let ctx := map (fun x => E.Build_context_decl x.(E.binder_name) None) (rev args) in
  "let " ++ decl ++ " = " ++  LPretty.print_term Σ [] TT ctx true false body.

Program Definition erase_check_debox_all_print (TT : env string) (decl_name : string)
        (tys : list Ast.term) (p : Ast.program)
  : string :=
  let p := fix_program_universes p in
  let deboxed := erase_check_debox_all TT p in
  print_sum (print_EnvCheck (print_decl decl_name TT tys) deboxed).

Notation "'unfolded' d" :=
  ltac:(let y := eval unfold d in d in exact y) (at level 100, only parsing).

(** Returns a pair of a fully qualified name and a short name to use in the extracted code.
 Used in the case if we need to refer to a previously extracted constant in the same file *)
Definition local (t : Ast.term) : string * string :=
  let nm := Ast.from_option (to_name t) "Error (constant expected)" in
  (nm, unqual_name nm).

(** Returns a pair of a fully qualified name (if [t] is a constant) and a new name.
 Used in a similar way as [Extract Inlined Constant] of the standard extraction *)
Definition remap (t : Ast.term) (new_name : string) :  string * string :=
  let nm := Ast.from_option (to_name t) "Error (constant or inductive expected)" in
  (nm, new_name).

Record LiqDef :=
  mkLiqDef {ld_name : string; ld_type: term; ld_body : Ast.term}.

Definition opt_to_template {A} (o : option A) : TemplateMonad A:=
  match o with
  | Some v => ret v
  | None => tmFail "None"
  end.

Definition to_constant_decl (gd : option global_decl) :=
  match gd with
  | Some (ConstantDecl cst_body) => ret cst_body
  | Some (InductiveDecl cst_body) => tmFail "Error (constant expected, given inductive)"
  | None => tmFail "Error (expected Some constant, given None)"
  end.

Definition toDefWithEnv {A} (p : A)  :=
  t <- tmQuoteRec p ;;
  nm <- opt_to_template (to_name t.2) ;;
  cbody_o <- to_constant_decl (lookup_env t.1 nm) ;;
  cbody <- opt_to_template cbody_o.(cst_body) ;;
  ret (mkLiqDef nm cbody_o.(cst_type) cbody, t.1).



Definition toDef {A} (p : A)  :=
  t <- tmQuote p ;;
  nm <- opt_to_template (to_name t) ;;
  cbody_o <- tmQuoteConstant nm false ;;
  cbody <- opt_to_template cbody_o.(cst_body) ;;
  ret (mkLiqDef nm cbody_o.(cst_type) cbody).

Definition toLiquidityWithBoxes {A} (TT : env string) (p : A) :=
  d_e <- toDefWithEnv p ;;
  let '(liq_def, env) := d_e in
  liq_prog <- tmEval lazy (erase_print TT (env,liq_def.(ld_body))) ;;
  let liq_def_string := "let " ++ unqual_name liq_def.(ld_name) ++ " = " ++ liq_prog in
  ret liq_def_string.

About decompose_prod.

Definition toLiquidity {A} (TT : env string) (p : A) :=
  d_e <- toDefWithEnv p ;;
  let '(liq_def, env) := d_e in
  let decl_name := unqual_name liq_def.(ld_name) in
  (* FIXME: we should use erasure for types here *)
  let '(_,tys,_) := decompose_prod liq_def.(ld_type) in
  tmEval lazy
         (erase_check_debox_all_print TT decl_name tys (env,liq_def.(ld_body))).

Definition toLiquidityEnv {A} (TT : env string) (Σ : TemplateEnvironment.global_env)(p : A) :=
  d <- toDef p ;;
  let decl_name := unqual_name d.(ld_name) in
  (* FIXME: we should use erasure for types here *)
  let '(_,tys,_) := decompose_prod d.(ld_type) in
  tmEval lazy
         (erase_check_debox_all_print TT decl_name tys (Σ,d.(ld_body))).


Definition print_one_ind_body (TT : env string) (oibs : list one_inductive_body) :=
  match oibs with
  | [oib] => ret (print_inductive TT oib)
  | _ => tmFail "Only non-mutual inductives supported"
  end.

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
    inl (LPretty.print_term Σ' TT [] true false (afrer_erase t))
  | EnvError Σ' (AlreadyDeclared id) =>
    inr ("Already declared: " ++ id)
  | EnvError Σ' (IllFormedDecl id e) =>
    inr ("Type error: " ++ PCUICSafeChecker.string_of_type_error Σ' e ++ ", while checking " ++ id)
  end.

Definition erase_print (TT : env string) (p : Ast.program) : string :=
  match erase_and_print_template_program TT id p with
  | inl s => s
  | inr s => s
  end.

Definition erase_print_deboxed (TT : env string) (p : Ast.program) : string :=
  match erase_and_print_template_program TT (debox []) p with
  | inl s => s
  | inr s => s
  end.

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
  mkLiqDef {ld_name : string; ld_type: term; ld_body : term}.

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

Definition toLiquidityWithBoxes {A} (TT : env string) (p : A) :=
  d_e <- toDefWithEnv p ;;
  let '(liq_def, env) := d_e in
  liq_prog <- tmEval all (erase_print TT (env,liq_def.(ld_body))) ;;
  let liq_def_string := "let " ++ unqual_name liq_def.(ld_name) ++ " = " ++ liq_prog in
  ret liq_def_string.


Definition toLiquidity {A} (TT : env string) (p : A) :=
  d_e <- toDefWithEnv p ;;
  let '(liq_def, env) := d_e in
  liq_prog <- tmEval all (erase_print_deboxed TT (env,liq_def.(ld_body))) ;;
  let liq_def_string := "let " ++ unqual_name liq_def.(ld_name) ++ " = " ++ liq_prog in
  ret liq_def_string.

Definition get_one_ind_body (TT : env string) (oibs : list one_inductive_body) :=
  match oibs with
  | [oib] => ret (print_inductive TT oib)
  | _ => tmFail "Only non-mutual inductives supported"
  end.

From Coq Require Import Arith.
From Coq Require Import Ascii.
From Coq Require Import List.
From Coq Require Import NArith.
From Coq Require Import String.

From MetaCoq Require Import monad_utils.
From MetaCoq Require Import MCPrelude.
From MetaCoq Require Import MCProd.
From MetaCoq Require Import MCString.
From MetaCoq Require Import MCSquash.
From MetaCoq.Erasure Require Import EAst.
From MetaCoq.Erasure Require Import SafeErasureFunction.
From MetaCoq.Erasure Require Import SafeTemplateErasure.
From MetaCoq.PCUIC Require Import PCUICAst PCUICTyping PCUICValidity TemplateToPCUIC.
From MetaCoq.SafeChecker Require Import PCUICSafeChecker.
From MetaCoq.SafeChecker Require Import SafeTemplateChecker.
From MetaCoq.Template Require Import Ast.
From MetaCoq.Template Require Import BasicAst.
From MetaCoq.Template Require Import Loader.
From MetaCoq.Template Require Import TemplateMonad.

From ConCert.Extraction Require Import ClosedAux.
From ConCert.Extraction Require Import Erasure.
From ConCert.Extraction Require Import ResultMonad.
From ConCert.Extraction Require Import Optimize.
From ConCert.Extraction Require Import OptimizeCorrectness.
From ConCert.Utils Require Import StringExtra.

Module T := MetaCoq.Template.Ast.
Module P := MetaCoq.PCUIC.PCUICAst.
Module E := MetaCoq.Erasure.EAst.
Module TUtil := MetaCoq.Template.AstUtils.
Module PUtil := MetaCoq.PCUIC.PCUICAstUtils.
Module PT := MetaCoq.PCUIC.PCUICTyping.
Module EF := MetaCoq.Erasure.SafeErasureFunction.
Module T2P := MetaCoq.PCUIC.TemplateToPCUIC.

Local Open Scope string.
Import ListNotations.
Import MonadNotation.

Local Open Scope bool.
Import E.

(** Extracts a constant name, inductive name or returns None *)
Definition to_kername (t : Ast.term) : option kername :=
  match t with
  | Ast.tConst c _ => Some c
  | Ast.tInd c _ => Some c.(inductive_mind)
  | _ => None
  end.

Notation "<%% t %%>" :=
  (ltac:(let p y :=
             let e := eval cbv in (to_kername y) in
             match e with
             | @Some _ ?kn => exact kn
             | _ => fail "not a name"
             end in quote_term t p)).

Definition result_of_typing_result
           {A}
           (Σ : P.global_env_ext)
           (tr : typing_result A) : result A string :=
  match tr with
  | Checked a => ret a
  | TypeError err => Err (string_of_type_error Σ err)
  end.

Definition string_of_env_error Σ e :=
  match e with
  | IllFormedDecl s e =>
    "IllFormedDecl " ++ s ++ "\nType error: " ++ string_of_type_error Σ e
  | AlreadyDeclared s => "Alreadydeclared " ++ s
  end%string.

Definition result_of_EnvCheck {A} (ec : EnvCheck A) : result A string :=
  match ec with
  | CorrectDecl a => ret a
  | EnvError Σ err => Err (string_of_env_error Σ err)
  end.

Definition result_of_option {A} (o : option A) (err : string) : result A string :=
  match o with
  | Some a => ret a
  | None => Err err
  end.

Definition to_string_name (t : Ast.term) : string :=
  match to_kername t with
  | Some kn => string_of_kername kn
  | None => "Not a constant or inductive"
  end.

Definition extract_def_name {A : Type} (a : A) : TemplateMonad kername :=
  a <- tmEval cbn a;;
  quoted <- tmQuote a;;
  let (head, args) := TUtil.decompose_app quoted in
  match head with
  | T.tConst name _ => ret name
  | _ => tmFail ("Expected constant at head, got " ++ TUtil.string_of_term head)
  end.

Notation "'unfolded' d" :=
  ltac:(let y := eval unfold d in d in exact y) (at level 100, only parsing).

Definition remap (kn : kername) (new_name : string) : kername * string :=
  (kn, new_name).

Definition EnvCheck_to_template {A } (ec : EnvCheck A) : TemplateMonad A :=
  match ec with
  | CorrectDecl a => ret a
  | EnvError Σ e => tmFail (string_of_env_error Σ e)
  end.

Definition quote_recursively_body {A : Type} (def : A) : TemplateMonad T.program :=
  p <- tmQuoteRecTransp def false ;;
  kn <- match p.2 with
       | T.tConst name _ => ret name
       | _ => tmFail ("Expected constant, got "  ++
                       TUtil.string_of_term p.2)
       end;;
  match T.lookup_env p.1 kn with
  | Some (T.ConstantDecl cb) =>
    match cb.(T.cst_body) with
    | Some b => ret (p.1, b)
    | None => tmFail ("The constant doesn't have a body: " ++ kn.2)
    end
  | _ => tmFail ("Not found: " ++ kn.2)
  end.

Fixpoint update_global_env (Σ :T.global_env) (Σup : T.global_env) : T.global_env :=
  match Σ with
  | (kn, gd) :: Σ' => match T.lookup_env Σup kn with
                    | Some v => (kn,v) :: update_global_env Σ' Σup
                    | None => (kn, gd) :: update_global_env Σ' Σup
                    end
  | [] => []
  end.

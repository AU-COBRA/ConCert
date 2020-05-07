From ConCert.Execution Require Import Blockchain.
From ConCert.Execution Require Import Serializable.
From ConCert.Execution Require Import Containers.
From ConCert.Execution Require Import Congress.
From ConCert.Extraction Require Import Certified.

From Coq Require Import List.
From Coq Require Import String.
From Coq Require Import ZArith.

From MetaCoq.Erasure Require Import Debox Loader SafeTemplateErasure.
From MetaCoq.SafeChecker Require Import Loader PCUICSafeChecker SafeTemplateChecker.
From MetaCoq.Template Require Import All.

Import ListNotations.
Import MonadNotation.

Section Counter.
Context {BaseTypes : ChainBase}.

Definition Setup := unit.

Inductive Msg :=
| increment
| decrement.

Definition State := Z.

Global Instance Serializable_Msg : Serializable Msg :=
  Derive Serializable Msg_rect<increment, decrement>.

Local Open Scope Z.
Definition init
           (chain : Chain)
           (ctx : ContractCallContext)
           (setup : Setup) : option State :=
  Some 0%Z.

Definition receive
           (chain : Chain)
           (ctx : ContractCallContext)
           (state : State)
           (maybe_msg : option Msg)
  : option (State * list ActionBody) :=
  match maybe_msg with
  | Some increment => Some (state + 1, [])
  | Some decrement => Some (state - 1, [])
  | _ => None
  end.

Program Definition contract : Contract Setup Msg State :=
  {| Blockchain.init := init; Blockchain.receive := receive; |}.

End Counter.

Local Open Scope nat.

(*
Fixpoint erasable_program (name : qualid) : TemplateMonad program :=
  cst <- tmQuoteConstant name false;;
  let body := cst_body cst in
  match body with
  | None => tmFail ("cannot get body of constant " ++ name)
  | Some body =>
    (fix aux (tries : nat) (env : global_env) : TemplateMonad program :=
    match tries with
    | 0 => tmFail "out of fuel"
    | S tries =>
      let p := (env, body) in
      result <- tmEval lazy (check_applied p);;
      match result with
      | CorrectDecl _ => ret p
      | EnvError Σ (IllFormedDecl _ e)  =>
        match e with
        | UndeclaredConstant c =>
          tmMsg ("need constant " ++ c);;
          cst <- tmQuoteConstant c false;;
          let cst := {| cst_type := cst_type cst;
                        cst_body := None;
                        cst_universes :=
                          Monomorphic_ctx (LevelSetProp.of_list [], ConstraintSet.empty); |} in
          let env := List.filter (fun '(n, _) => negb (n =? c)%string) env in
          aux tries ((c, ConstantDecl cst) :: env)
        | UndeclaredInductive c
        | UndeclaredConstructor c _ =>
          let name := inductive_mind c in
          tmMsg ("need inductive " ++ name);;
          ind <- tmQuoteInductive name;;
          let ind := {| ind_finite := ind_finite ind;
                        ind_npars := ind_npars ind;
                        ind_params := ind_params ind;
                        ind_bodies := ind_bodies ind;
                        ind_universes :=
                          Monomorphic_ctx (LevelSetProp.of_list [], ConstraintSet.empty);
                        ind_variance := ind_variance ind |} in
          let env := List.filter (fun '(n, _) => negb (n =? name)%string) env in
          aux tries ((name, InductiveDecl ind) :: env)
        | _ =>
          tmFail (string_of_type_error Σ e)
        end
      | EnvError Σ (AlreadyDeclared id) =>
        tmFail ("Already declared: " ++ id)
      end
    end) 1000 []
  end.

Definition erase_and_print p : TemplateMonad unit :=
  match erase_and_print_template_program p with
  | inl s => tmMsg s
  | inr s => tmMsg s
  end.
*)

Axiom extraction_chain_base : ChainBase.

Definition extract_def_name {A : Type} (a : A) : TemplateMonad qualid :=
  a <- tmEval cbn a;;
  quoted <- tmQuote a;;
  let (head, args) := decompose_app quoted in
  match head with
  | tConst name _ => ret name
  | _ => tmFail ("Expected constant at head, got " ++ string_of_term head)
  end.

Definition toMidlang
           {Setup Msg State}
           `{Serializable Setup}
           `{Serializable Msg}
           `{Serializable State}
           (contract : forall (cb : ChainBase), Contract Setup Msg State) : TemplateMonad unit :=
  init <- tmEval cbn (Blockchain.init (contract extraction_chain_base));;
  recv <- tmEval cbn (Blockchain.receive (contract extraction_chain_base));;
  p <- tmQuoteRec (init, recv);;

  init_name <- extract_def_name (Blockchain.init (contract extraction_chain_base));;
  receive_name <- extract_def_name (Blockchain.receive (contract extraction_chain_base));;
  x <- erasable_program receive_name;;
  tmMsg (string_of_term x.2).

Run TemplateProgram (toMidlang (fun cb => @contract cb)).

Definition test : TemplateProgram unit :=
  tmEval

Definition foo (m : FMap nat nat) : option nat :=
  FMap.find 3 m.

Run TemplateProgram (erasable_program "Congress.receive").

Run TemplateProgram (
  x <- erasable_program "Congress.receive";;
  s <- tmEval lazy (erase_check_debox_all_print [] "foo" [] x);;
  tmMsg s).

Run TemplateProgram (erasable_program "stdpp.base.lookup" >>= tmPrint).

Run TemplateProgram (
  x <- erasable_program "stdpp.base.lookup";;
  s <- tmEval lazy (erase_check_debox_all_print [] "stdpp.base.lookup" [] x);;
  tmMsg s).

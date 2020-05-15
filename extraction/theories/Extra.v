 (* TODO : delete this when we merge proper utilities to fetch dependencies *)
From Coq Require Import List.
From Coq Require Import String.

From MetaCoq Require Import monad_utils.
From MetaCoq.Template Require Import All.
From MetaCoq.SafeChecker Require Import PCUICSafeChecker.

From ConCert.Extraction Require Import Certified.
Import MonadNotation.
Import ListNotations.

Fixpoint erasable_program (name : ident) : TemplateMonad program :=
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

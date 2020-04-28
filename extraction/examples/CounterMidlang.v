From ConCert.Execution Require Import Blockchain.
From ConCert.Execution Require Import Serializable.
From ConCert.Execution Require Import Containers.
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

Definition add_inductive_if_new
           (ind : inductive)
           (globals : global_env) : TemplateMonad (global_env * list TemplateTerm.term) :=
  let name := inductive_mind ind in
  if existsb (fun '(n, _) => (n =? name)%string) globals then
    ret (globals, [])
  else
    tmMsg ("adding type " ++ name);;
    ind <- tmQuoteInductive name;;
    let context_decl_terms cdecl :=
        match decl_body cdecl with
        | Some a => [a; decl_type cdecl]
        | None => [decl_type cdecl]
        end in
    let inductive_body_terms ibody :=
        let ctors := map (fun '((_, t), _) => t) (ind_ctors ibody) in
        let projs := map snd (ind_projs ibody) in
        ind_type ibody :: ctors ++ projs in
    let terms := flat_map context_decl_terms (ind_params ind) in
    let terms := (flat_map inductive_body_terms (ind_bodies ind) ++ terms)%list in
    ret ((name, InductiveDecl ind) :: globals, terms).

Local Open Scope positive.
Fixpoint hex_of_positive (p : positive) : string :=
  match p with
  | xH => "1"
  | xH~0 => "2"
  | xH~1 => "3"
  | xH~0~0 => "4"
  | xH~0~1 => "5"
  | xH~1~0 => "6"
  | xH~1~1 => "7"
  | xH~0~0~0 => "8"
  | xH~0~0~1 => "9"
  | xH~0~1~0 => "a"
  | xH~0~1~1 => "b"
  | xH~1~0~0 => "c"
  | xH~1~0~1 => "d"
  | xH~1~1~0 => "e"
  | xH~1~1~1 => "f"
  | p~0~0~0~0 => hex_of_positive p ++ "0"
  | p~0~0~0~1 => hex_of_positive p ++ "1"
  | p~0~0~1~0 => hex_of_positive p ++ "2"
  | p~0~0~1~1 => hex_of_positive p ++ "3"
  | p~0~1~0~0 => hex_of_positive p ++ "4"
  | p~0~1~0~1 => hex_of_positive p ++ "5"
  | p~0~1~1~0 => hex_of_positive p ++ "6"
  | p~0~1~1~1 => hex_of_positive p ++ "7"
  | p~1~0~0~0 => hex_of_positive p ++ "8"
  | p~1~0~0~1 => hex_of_positive p ++ "9"
  | p~1~0~1~0 => hex_of_positive p ++ "a"
  | p~1~0~1~1 => hex_of_positive p ++ "b"
  | p~1~1~0~0 => hex_of_positive p ++ "c"
  | p~1~1~0~1 => hex_of_positive p ++ "d"
  | p~1~1~1~0 => hex_of_positive p ++ "e"
  | p~1~1~1~1 => hex_of_positive p ++ "f"
  end.

Local Open Scope nat.
Definition hex_of_nat (n : nat) : string :=
  match n with
  | 0 => "0"
  | S n => hex_of_positive (Pos.of_succ_nat n)
  end.

Fixpoint get_globals
         (fuel : nat)
         (terms : list TemplateTerm.term)
         (globals : global_env) : TemplateMonad global_env :=
  tmMsg ("fuel " ++ hex_of_nat fuel);;
  match terms, fuel with
  | [], _ => ret globals
  | _, 0 => tmFail "out of fuel"
  | term :: terms, S fuel =>
    match term with
    | tEvar _ ts => get_globals fuel (ts ++ terms) globals
    | tCast t1 _ t2
    | tProd _ t1 t2
    | tLambda _ t1 t2 => get_globals fuel (t1 :: t2 :: terms) globals
    | tLetIn _ t1 t2 t3 => get_globals fuel (t1 :: t2 :: t3 :: terms) globals
    | tApp t1 ts => get_globals fuel (t1 :: ts ++ terms) globals
    | tConst name _ =>
      if existsb (fun '(n, _) => (n =? name)%string) globals then
        get_globals fuel terms globals
      else
        cst <- tmQuoteConstant name false;;
        let globals := (name, ConstantDecl cst) :: globals in
        match cst_body cst with
        | Some body => get_globals fuel (body :: cst_type cst :: terms) globals
        | None => get_globals fuel terms globals
        end
    | tInd ind _
    | tConstruct ind _ _ =>
      '(globals, ind_terms) <- add_inductive_if_new ind globals;;
      get_globals fuel (ind_terms ++ terms) globals
    | tCase _ t1 t2 ts => get_globals fuel (t1 :: t2 :: map snd ts ++ terms) globals
    | tProj ((ind, _), _) t =>
      '(globals, ind_terms) <- add_inductive_if_new ind globals;;
      get_globals fuel (t :: ind_terms ++ terms) globals
    | tFix f _
    | tCoFix f _ => get_globals fuel (map dbody f ++ terms) globals
    | _ => get_globals fuel terms globals
    end
  end.

Definition quote_rec (name : string) : TemplateMonad program :=
  cst <- tmQuoteConstant name false;;
  term <-
  match cst_body cst with
  | Some term => ret term
  | None => tmFail (name ++ " does not have a body")
  end;;
  globals <- get_globals (N.to_nat 100000) [term] [];;
  ret (globals, term).

Fixpoint erasable_program (name : string) : TemplateMonad program :=
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
      match check_applied p with
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

Definition remove_universes (p : program) : program :=
  let remove_constraints udecl :=
      match udecl with
      | Monomorphic_ctx (levels, _) => Monomorphic_ctx (LevelSetProp.of_list [], ConstraintSet.empty)
      | Polymorphic_ctx (names, _) => Polymorphic_ctx ([], ConstraintSet.empty)
      end in
  let remove g :=
      match g with
      | ConstantDecl cst =>
        ConstantDecl
          {| cst_type := cst_type cst;
             cst_body := cst_body cst;
             cst_universes := remove_constraints (cst_universes cst) |}
      | InductiveDecl ind =>
        InductiveDecl
          {| ind_finite := ind_finite ind;
             ind_npars := ind_npars ind;
             ind_params := ind_params ind;
             ind_bodies := ind_bodies ind;
             ind_universes := remove_constraints (ind_universes ind);
             ind_variance := ind_variance ind |}
      end in
  let (env, term) := p in
  (map (fun '(n, g) => (n, remove g)) env, term).

Run TemplateProgram

Run TemplateProgram (
  p <- erasable_program "contract";;
  tmMsg (erase_print_deboxed [] p)).

Run TemplateProgram (
  x <- erasable_program "contract";;
  s <- tmEval lazy (erase_check_debox_all_print [] "foo" [] x);;
  tmMsg s).

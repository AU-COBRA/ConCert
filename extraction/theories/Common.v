From Coq Require Import Arith.
From Coq Require Import Ascii.
From Coq Require Import List.
From Coq Require Import NArith.
From Coq Require Import String.

From MetaCoq Require Import monad_utils.
From MetaCoq Require Import MCProd.
From MetaCoq Require Import MCString.
From MetaCoq Require Import MCSquash.
From MetaCoq.Erasure Require Import Debox.
From MetaCoq.Erasure Require Import EAst.
From MetaCoq.Erasure Require Import SafeErasureFunction.
From MetaCoq.Erasure Require Import SafeTemplateErasure.
From MetaCoq.PCUIC Require Import PCUICAst.
From MetaCoq.SafeChecker Require Import PCUICSafeChecker.
From MetaCoq.SafeChecker Require Import SafeTemplateChecker.
From MetaCoq.Template Require Import Ast.
From MetaCoq.Template Require Import BasicAst.
From MetaCoq.Template Require Import Loader.
From MetaCoq.Template Require Import TemplateMonad.

From ConCert.Execution Require Import Blockchain.
From ConCert.Execution Require Import Serializable.
From ConCert.Extraction Require Import Certified.
From ConCert.Extraction Require Import ResultMonad.
From ConCert.Extraction Require Import StringExtra.

Module T := MetaCoq.Template.Ast.
Module P := MetaCoq.PCUIC.PCUICAst.
Module E := MetaCoq.Erasure.EAst.
Module D := MetaCoq.Erasure.Debox.
Module TUtil := MetaCoq.Template.AstUtils.
Module PT := MetaCoq.PCUIC.PCUICTyping.
Module EF := MetaCoq.Erasure.SafeErasureFunction.
Module T2P := MetaCoq.PCUIC.TemplateToPCUIC.

Local Open Scope string.
Import ListNotations.
Import MonadNotation.

Module Export Ex.
  Record constant_body :=
    { cst_type : P.term;
      cst_body : option E.term; }.

  Record one_inductive_body :=
    { ind_name : ident;
      ind_type_parameters : list name;
      ind_ctors : list (ident * list D.box_type);
      ind_projs : list (ident * D.box_type); }.

  Record mutual_inductive_body :=
    { ind_bodies : list one_inductive_body; }.

  Inductive global_decl :=
  | ConstantDecl : constant_body -> global_decl
  | InductiveDecl : mutual_inductive_body -> global_decl.

  Definition global_env := list (kername * global_decl).

  Fixpoint lookup_env (Σ : global_env) (id : ident) : option global_decl :=
    match Σ with
    | [] => None
    | (name, decl) :: Σ => if ident_eq id name then Some decl else lookup_env Σ id
    end.
End Ex.

Definition kername_unqual (name : kername) : string :=
  match last_index_of "." name with
  | Some n => substring_from (S n) name
  | None => name
  end.

Definition kername_qualifier (name : kername) : string :=
  match last_index_of "." name with
  | Some n => substring_count n name
  | None => ""
  end.

Import E.
Fixpoint ungeneralize_ChainBase_aux (cb_arg : nat) (t : term) : result term string :=
    match t with
    | tBox _ => ret t
    | tRel n =>
      if (n =? cb_arg)%nat then
        Err "term contains unhandled use of ChainBase"
      else
        ret t
    | tVar _ => ret t
    | tEvar n ts =>
      ts <- monad_map (ungeneralize_ChainBase_aux cb_arg) ts;;
      ret (tEvar n ts)
    | tLambda name t =>
      t <- ungeneralize_ChainBase_aux (S cb_arg) t;;
      ret (tLambda name t)
    | tLetIn name val body =>
      val <- ungeneralize_ChainBase_aux cb_arg val;;
      body <- ungeneralize_ChainBase_aux (S cb_arg) body;;
      ret (tLetIn name val body)
    | tApp (tConst _ as head) (tRel i) =>
      if (i =? cb_arg)%nat then
        ret head
      else
        ret t
    | tApp head arg =>
      head <- ungeneralize_ChainBase_aux cb_arg head;;
      arg <- ungeneralize_ChainBase_aux cb_arg arg;;
      ret (tApp head arg)
    | tConst _ => ret t
    | tConstruct _ _ => ret t
    | tCase ind disc brs =>
      disc <- ungeneralize_ChainBase_aux cb_arg disc;;
      brs <- monad_map (fun '(arity, body) => body <- ungeneralize_ChainBase_aux cb_arg body;;
                                              ret (arity, body)) brs;;
      ret (tCase ind disc brs)
    | tProj proj body =>
      body <- ungeneralize_ChainBase_aux cb_arg body;;
      ret (tProj proj body)
    | tFix defs i =>
      let cb_arg := (List.length defs + cb_arg)%nat in
      defs <- monad_map (fun (d : def term) =>
                           dbody <- ungeneralize_ChainBase_aux cb_arg (dbody d);;
                           ret {| dname := dname d;
                                  dbody := dbody;
                                  rarg := rarg d |}) defs;;
      ret (tFix defs i)
    | tCoFix defs i =>
      let cb_arg := (List.length defs + cb_arg)%nat in
      defs <- monad_map (fun (d : def term) =>
                           dbody <- ungeneralize_ChainBase_aux cb_arg (dbody d);;
                           ret {| dname := dname d;
                                  dbody := dbody;
                                  rarg := rarg d |}) defs;;
      ret (tCoFix defs i)
    end.

(* Remove all generalization over ChainBase *)
Definition ungeneralize_ChainBase
           (type : P.term)
           (body : E.term) : result (P.term * E.term) string :=
  match type, body with
  | P.tProd _ (P.tInd ind _) it, E.tLambda _ ib =>
    if inductive_mind ind =? "ConCert.Execution.Blockchain.ChainBase" then
      ib <- ungeneralize_ChainBase_aux 0 ib;;
      ret (it, ib)
    else
      ret (type, body)
  | _, _ => ret (type, body)
  end.

From ConCert.Execution Require Blockchain.
(* This is here so that we get a typing error if Chain ever changes *)
Check (fun _ => eq_refl) :
  forall chain,
    Blockchain.account_balance chain = let (_, _, _, f) := chain in f.
Local Open Scope bool.
(* Check if term destructs 'Chain' anywhere and uses the
account_balance field *)
Import E.
Definition uses_account_balance (t : term) : bool :=
  (fix f (t : term) (ab_funcs : list bool) :=
     match t with
     | tBox _ => false
     | tRel i => nth i ab_funcs false
     | tVar _ => false
     | tEvar _ ts => fold_left (fun b t => b || f t ab_funcs) ts false
     | tLambda _ t => f t (false :: ab_funcs)
     | tLetIn _ val body => f val ab_funcs || f body (false :: ab_funcs)
     | tApp head body => f head ab_funcs || f body ab_funcs
     | tConst _ => false
     | tConstruct _ _ => false
     | tCase (ind, _) disc brs =>
       f disc ab_funcs ||
       if inductive_mind ind =? "ConCert.Execution.Blockchain.Chain" then
         match brs with
         | [(4, tLambda _ (tLambda _ (tLambda _ (tLambda _ t))))] =>
           f t (true :: false :: false :: false :: ab_funcs)
         | _ => fold_left (fun b '(_, t) => b || f t ab_funcs) brs false
         end
       else
         fold_left (fun b '(_, t) => b || f t ab_funcs) brs false
     | tProj _ t => f t ab_funcs
     | tFix defs _
     | tCoFix defs _ =>
       let ab_funcs := (repeat false (List.length defs) ++ ab_funcs)%list in
       fold_left (fun b d => b || f (dbody d) ab_funcs) defs false
     end) t [].

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

Axiom assump : string -> forall {A}, A.

(* Change an inductive type from A -> B -> Type into A -> B -> unit
   to allow us to use type erasure on it *)
Fixpoint recast_into_unit (n : nat) (t : P.term) : option P.term :=
  match n, t with
  | 0, P.tSort _ => ret (P.tInd (mkInd "Coq.Init.Datatypes.unit" 0) [])
  | S n, P.tProd name arg_ty body =>
    t <- recast_into_unit n body;;
    ret (P.tProd name arg_ty t)
  | _, _ => None
  end.

Import Ex.
Definition erase_and_debox_ind_ctor
           (Σ : P.global_env_ext)
           (wfΣ : ∥PT.wf_ext Σ∥)
           (Γ : P.context)
           (npars : nat)
           (p : ident * P.term * nat) : result (ident * list D.box_type) string :=
  let '(name, ty, _) := p in
  '(type_names, bty) <-
  result_of_typing_result
    Σ
    (erase_type Σ wfΣ Γ
                (map Some (seq 0 (List.length Γ)))
                []
                (List.length Γ)
                false
                ty
                (assump "assuming well-typedness"));;
  (if (List.length type_names =? npars)%nat then
     ret tt
   else
     Err "inductive constructor is too general");;
  let bty := debox_box_type bty in
  let (btys, _) := decompose_arr bty in
  ret (name, btys).

Definition erase_and_debox_one_inductive_body
           (Σ : P.global_env_ext)
           (wfΣ : ∥PT.wf_ext Σ∥)
           (Γ : P.context)
           (npars : nat)
           (oib : P.one_inductive_body) : result one_inductive_body string :=
  t <- result_of_option (recast_into_unit npars (P.ind_type oib))
                        ("could not recast inductive type '"
                           ++ P.ind_name oib ++ "' into unit"
                           ++ nl ++ PCUICAstUtils.string_of_term (P.ind_type oib));;
  '(type_names, _) <-
  result_of_typing_result
    Σ
    (erase_type Σ wfΣ [] [] [] 0 false t (assump "assuming well-typedness"));;
  ctors <- monad_map (erase_and_debox_ind_ctor Σ wfΣ Γ npars) (P.ind_ctors oib);;
  (if 0 <? List.length (P.ind_projs oib) then Err "cannot handle projections yet" else Ok tt);;
  ret {| ind_name := P.ind_name oib;
         ind_type_parameters := type_names;
         ind_ctors := ctors;
         ind_projs := []; |}.

Lemma proj_wf
      {Σ : P.global_env_ext}
      (wfΣ : ∥PT.wf_ext Σ∥) : ∥PT.wf Σ.1∥.
Proof. firstorder. Qed.

Definition erase_and_debox_term
           (Σ : P.global_env_ext)
           (wfΣ : ∥PT.wf_ext Σ∥)
           (t : P.term) : result E.term string :=
  et <- result_of_typing_result
          Σ
          (EF.erase Σ wfΣ [] t (assump "assuming well-typedness"));;
  result <- result_of_EnvCheck (check_applied Σ.1 et (proj_wf wfΣ));;
  if result : bool then
    ret (debox_all et)
  else
    Err "Not all constructors or constants are appropriately applied".

Definition erase_and_debox_single
           (Σ : P.global_env_ext)
           (wfΣ : ∥PT.wf_ext Σ∥)
           (decl : P.global_decl) : result global_decl string :=
  match decl with
  | P.ConstantDecl cst =>
    let (type, body, _) := cst in
    match body with
    | None => ret (ConstantDecl {| cst_type := type; cst_body := None |})
    | Some body =>
      ebody <- erase_and_debox_term Σ wfΣ body;;
      let ebody := debox_top_level ebody in
      ret (ConstantDecl {| cst_type := type; cst_body := Some ebody |} )
    end
  | P.InductiveDecl mib =>
    let Γ := P.arities_context (P.ind_bodies mib) in
    bodies <- monad_map (erase_and_debox_one_inductive_body Σ wfΣ Γ (P.ind_npars mib))
                        (P.ind_bodies mib);;
    ret (InductiveDecl {| ind_bodies := bodies |})
  end.

Definition add_seen (n : kername) (seen : list kername) : list kername :=
  if existsb (String.eqb n) seen then
    seen
  else
    n :: seen.

Module EDeps.
Import E.
Fixpoint term_deps (seen : list kername) (t : term) : list kername :=
  match t with
  | tBox _
  | tRel _
  | tVar _ => seen
  | tEvar _ ts => fold_left term_deps ts seen
  | tLambda _ t => term_deps seen t
  | tLetIn _ t1 t2
  | tApp t1 t2 => term_deps (term_deps seen t1) t2
  | tConst n => add_seen n seen
  | tConstruct ind _ => add_seen (inductive_mind ind) seen
  | tCase (ind, _) t brs =>
    let seen := term_deps (add_seen (inductive_mind ind) seen) t in
    fold_left (fun seen '(_, t) => term_deps seen t) brs seen
  | tProj (ind, _, _) t => term_deps (add_seen (inductive_mind ind) seen) t
  | tFix defs _
  | tCoFix defs _ =>
    fold_left (fun seen d => term_deps seen (dbody d)) defs seen
  end.
End EDeps.

Module DDeps.
Import D.
Fixpoint box_type_deps (seen : list kername) (t : box_type) : list kername :=
  match t with
  | TBox _ => seen
  | TArr t1 t2
  | TApp t1 t2 => fold_left box_type_deps [t1; t2] seen
  | TRel _ => seen
  | TInd ind => add_seen (inductive_mind ind) seen
  | TConst n => add_seen n seen
  end.
End DDeps.

Import Ex.
Definition decl_deps (decl : global_decl) : list kername :=
  match decl with
  | ConstantDecl body =>
    match cst_body body with
    | Some body => EDeps.term_deps [] body
    | None => []
    end
  | InductiveDecl mib =>
    let one_inductive_body_deps seen oib :=
        let seen := fold_left DDeps.box_type_deps
                              (flat_map snd (ind_ctors oib))
                              seen in
        fold_left DDeps.box_type_deps (map snd (ind_projs oib)) seen in
    fold_left one_inductive_body_deps (ind_bodies mib) []
  end.

(* Erase and debox the graph of unignored dependencies starting with
   the specified seeds. Return a list of all required dependencies in
   topological order. The global environment is assumed to type check *)
Definition erase_and_debox_graph
           (Σ : P.global_env_ext)
           (wfΣ : ∥PT.wf_ext Σ∥)
           (seeds : list kername)
           (ignore : list kername) : result global_env string :=
  let fix go n (p : list (kername * global_decl) * list kername) name :=
      let (result, seen) := p in
      match n with
      | 0 => Err "out of fuel"
      | S n =>
        if existsb (String.eqb name) (ignore ++ seen) then
          ret (result, seen)
        else
          match PT.lookup_env Σ.1 name with
          | Some decl =>
            (* Add this to the set of seen declarations immediately so we don't revisit.
               However, we wait with adding it to the result set to make sure we add all
               dependencies first. *)
            let seen := name :: seen in
            erased_decl <- match erase_and_debox_single Σ wfΣ decl with
                           | Ok d => Ok d
                           | Err s => Err ("Error while erasing and deboxing '"
                                             ++ name ++ "'" ++ nl ++ s)
                           end;;
            '(result, seen) <- monad_fold_left (go n) (decl_deps erased_decl) (result, seen);;
            ret ((name, erased_decl) :: result, seen)
          | None => Err ("a seed recursively depends on '"
                           ++ name ++ "' which could not be found in the environment")
          end
      end in
  '(result, _) <- monad_fold_left (go (N.to_nat 10000)) seeds ([], []);;
  ret (rev result).

Lemma wf_empty_ext (Σ : P.global_env) :
  ∥PT.wf Σ∥ -> ∥PT.wf_ext (P.empty_ext Σ)∥.
Proof.
  intros [wfΣ].
  constructor.
  split; [assumption|].
  exact (assump "on_udecl on empty_ext").
Qed.

Definition check_template_env_for_erasure
           (Σ : T.global_env) :
  result { Σ : P.global_env_ext & ∥PT.wf_ext Σ∥ } string :=
  let remove_universe_constraints (decl : T.global_decl) :=
      match decl with
      | T.ConstantDecl body =>
        let (type, body, _) := body in
        T.ConstantDecl {| T.cst_type := type;
                          T.cst_body := body;
                          T.cst_universes := Monomorphic_ctx ContextSet.empty |}
      | T.InductiveDecl mib =>
        let (finite, npars, params, bodies, _, variance) := mib in
        T.InductiveDecl {| T.ind_finite := finite;
                           T.ind_npars := npars;
                           T.ind_params := params;
                           T.ind_bodies := bodies;
                           T.ind_universes := Monomorphic_ctx ContextSet.empty;
                           T.ind_variance := variance |}
      end in
  let Σ := map (fun '(name, d) => (name, remove_universe_constraints d)) Σ in
  let Σ := fix_global_env_universes Σ in
  let Σ := (T2P.trans_global (T.empty_ext Σ)).1 in
  G <- result_of_EnvCheck (check_wf_env_only_univs Σ);;
  let wfΣ := G.π2.p2 in
  let Σext := P.empty_ext Σ in
  let wfΣext := wf_empty_ext Σ wfΣ in
  ret (existT Σext wfΣext).

(* Erase and debox the specified template environment. This will
   recursively traverse all unignored dependencies of the specified
   seeds, and erase and debox only those. It returns the result in
   topological order. Assumption: the global environment type
   checks. *)
Definition erase_and_debox_template_env
           (Σ : T.global_env)
           (seeds : list kername)
           (ignore : list kername) : result global_env string :=
  '(existT Σext wfΣext) <- check_template_env_for_erasure Σ;;
  env <- erase_and_debox_graph Σext wfΣext seeds ignore;;
  ret env.

(* Like above, but get dependencies from the term of a template
   program, and also erase and debox the template program. *)
Definition erase_and_debox_template_program
           (p : T.program)
           (ignore : list kername) : result (global_env * E.term) string :=
  '(existT Σext wfΣext) <- check_template_env_for_erasure p.1;;
  term <- erase_and_debox_term Σext wfΣext (T2P.trans p.2);;
  let deps := EDeps.term_deps [] term in
  env <- erase_and_debox_graph Σext wfΣext deps ignore;;
  ret (env, term).

Definition ignored_concert_types :=
  ["ConCert.Execution.Blockchain.ChainBase";
   "ConCert.Execution.Blockchain.Chain";
   "ConCert.Execution.Blockchain.ContractCallContext"].

Import T.
Definition extract_def_name {A : Type} (a : A) : TemplateMonad qualid :=
  a <- tmEval cbn a;;
  quoted <- tmQuote a;;
  let (head, args) := TUtil.decompose_app quoted in
  match head with
  | tConst name _ => ret name
  | _ => tmFail ("Expected constant at head, got " ++ TUtil.string_of_term head)
  end.

Axiom extraction_chain_base : ChainBase.

Record ContractExtractionSet :=
  { env : Ex.global_env;
    init_name : kername;
    receive_name : kername; }.

Definition preprocess_for_extraction '(name, decl) : result (kername * Ex.global_decl) string :=
  match decl with
  | Ex.ConstantDecl body =>
    let (ty, body) := body in
    match body with
    | None => ret (name, Ex.ConstantDecl {| Ex.cst_type := ty; Ex.cst_body := None |})
    | Some body =>
      if uses_account_balance body then
        Err ("'" ++ name ++ "' uses account_balance")
      else
        '(type, body) <- ungeneralize_ChainBase ty body;;
        ret (name, Ex.ConstantDecl {| Ex.cst_type := type; Ex.cst_body := Some body |})
    end
  | _ => ret (name, decl)
  end.

Definition get_contract_extraction_set
           {Setup Msg State}
           `{Serializable Setup}
           `{Serializable Msg}
           `{Serializable State}
           (contract : forall (cb : ChainBase), Contract Setup Msg State)
  : TemplateMonad ContractExtractionSet :=
  init_name <- extract_def_name (Blockchain.init (contract extraction_chain_base));;
  receive_name <- extract_def_name (Blockchain.receive (contract extraction_chain_base));;
  p <- tmQuoteRec contract;;
  let seeds := [init_name; receive_name] in
  result <- tmEval lazy (erase_and_debox_template_env p.1 seeds ignored_concert_types
                         >>= monad_map preprocess_for_extraction);;
  match result with
  | Ok Σ => ret {| env := Σ; init_name := init_name; receive_name := receive_name; |}
  | Err err => tmFail err
  end.

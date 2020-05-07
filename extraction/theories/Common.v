From Coq Require Import Arith.
From Coq Require Import Ascii.
From Coq Require Import List.
From Coq Require Import NArith.
From Coq Require Import String.

From MetaCoq Require Import monad_utils.
From MetaCoq.Template Require Ast.
From MetaCoq.Template Require Import BasicAst.
From MetaCoq.PCUIC Require PCUICAst.
From MetaCoq.Erasure Require EAst.

From ConCert.Extraction Require Import ResultMonad.
From ConCert.Extraction Require Import StringExtra.

Module T := MetaCoq.Template.Ast.
Module P := MetaCoq.PCUIC.PCUICAst.
Module E := MetaCoq.Erasure.EAst.

Local Open Scope string.
Import ListNotations.
Import MonadNotation.

Record constant_body :=
  { cst_type : P.term;
    cst_body : option E.term; }.

Inductive global_decl :=
| ConstantDecl : constant_body -> global_decl
| InductiveDecl : P.mutual_inductive_body -> global_decl.

Definition global_env := list (kername * global_decl).

Fixpoint lookup_env (Σ : global_env) (id : ident) : option global_decl :=
  match Σ with
  | [] => None
  | (name, decl) :: Σ => if ident_eq id name then Some decl else lookup_env Σ id
  end.

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

Definition add_seen (n : kername) (seen : list kername) : list kername :=
  if existsb (String.eqb n) seen then
    seen
  else
    n :: seen.

Module EDeps.
Import E.
Fixpoint term_deps
         (seen : list kername)
         (t : term) : list kername :=
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

Module PDeps.
Import P.
Fixpoint term_deps
         (seen : list kername)
         (t : term) : list kername :=
  match t with
  | P.tRel _
  | P.tVar _ => seen
  | P.tEvar _ ts => fold_left term_deps ts seen
  | P.tSort _ => seen
  | P.tProd _ t1 t2 => fold_left term_deps [t1; t2] seen
  | P.tLambda _ t1 t2 => fold_left term_deps [t1; t2] seen
  | P.tLetIn _ t1 t2 t3 => fold_left term_deps [t1; t2; t3] seen
  | P.tApp t1 t2 => fold_left term_deps [t1; t2] seen
  | P.tConst n _ => add_seen n seen
  | P.tInd ind _ => add_seen (inductive_mind ind) seen
  | P.tConstruct ind _ _ => add_seen (inductive_mind ind) seen
  | P.tCase (ind, _) t1 t2 brs =>
    let seen := add_seen (inductive_mind ind) seen in
    let seen := fold_left term_deps [t1; t2] seen in
    fold_left (fun seen '(_, t) => term_deps seen t) brs seen
  | P.tProj (ind, _, _) t => term_deps (add_seen (inductive_mind ind) seen) t
  | P.tFix defs _
  | P.tCoFix defs _ =>
    fold_left (fun seen d => term_deps seen (BasicAst.dbody d)) defs seen
  end.
End PDeps.

Definition decl_deps (decl : global_decl) : list kername :=
  match decl with
  | ConstantDecl body =>
    match cst_body body with
    | Some body => EDeps.term_deps [] body
    | None => []
    end
  | InductiveDecl mib =>
    let one_inductive_body_deps seen oib :=
        let seen := fold_left (fun seen '(_, t, _) => PDeps.term_deps seen t)
                              (P.ind_ctors oib)
                              seen in
        fold_left (fun seen '(_, t) => PDeps.term_deps seen t) (P.ind_projs oib) seen in

    fold_left one_inductive_body_deps (P.ind_bodies mib) []
  end.

(* Return all recursive dependencies of the specified seed
   declarations in topological order *)
Definition decl_deps_recursive
           (Σ : global_env)
           (seeds : list kername)
           (ignore : list kername) : result (list (kername * global_decl)) string :=
  let fix go n (p : list (kername * global_decl) * list kername) name :=
      let (result, seen) := p in
      match n with
      | 0 => Err "out of fuel"
      | S n =>
        if existsb (String.eqb name) (ignore ++ seen) then
          ret (result, seen)
        else
          match lookup_env Σ name with
          | Some decl =>
            (* Add this to the set of seen declarations immediately so we don't revisit.
               However, we wait with adding it to the result set to make sure we add all
               dependencies first. *)
            let deps := decl_deps decl in
            let seen := name :: seen in
            '(result, seen) <- monad_fold_left (go n) (decl_deps decl) (result, seen);;
            ret ((name, decl) :: result, seen)
          | None => Err ("a seed recursively depends on '" ++ name ++
                         "' which could not be found in the environment")
          end
      end in
  '(result, _) <-
  monad_fold_left (go (N.to_nat 10000)) seeds ([], []);;
  (*deps <- slow_topological_sort Σ deps;;*)
  ret (rev result).

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
      defs <- monad_map (fun d =>
                           dbody <- ungeneralize_ChainBase_aux cb_arg (dbody d);;
                           ret {| dname := dname d;
                                  dbody := dbody;
                                  rarg := rarg d |}) defs;;
      ret (tFix defs i)
    | tCoFix defs i =>
      let cb_arg := (List.length defs + cb_arg)%nat in
      defs <- monad_map (fun d =>
                           dbody <- ungeneralize_ChainBase_aux cb_arg (dbody d);;
                           ret {| dname := dname d;
                                  dbody := dbody;
                                  rarg := rarg d |}) defs;;
      ret (tFix defs i)
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

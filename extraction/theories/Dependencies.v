From Coq Require Import List.
From MetaCoq.Erasure Require EAst.
From MetaCoq.Template Require Import All.

Import ListNotations.

Definition add_seen (n : kername) (seen : list kername) : list kername :=
  if existsb (String.eqb n) seen then
    seen
  else
    n :: seen.

Module EDeps.
Import EAst.

Fixpoint term_deps
         (seen : list kername)
         (t : term) : list kername :=
  match t with
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
  | _ => seen
  end.

Definition decl_deps (decl : Ex.global_decl) : list kername :=
  match decl with
  | Ex.ConstantDecl body =>
    match Ex.cst_body body with
    | Some body => term_deps [] body
    | None => []
    end
  | Ex.InductiveDecl _ emib =>
    let one_inductive_body_deps seen oib :=
        let seen := fold_left (fun seen '(_, t, _) => term_deps seen t) (ind_ctors oib) seen in
        fold_left (fun seen '(_, t) => term_deps seen t) (ind_projs oib) seen in

    fold_left one_inductive_body_deps (ind_bodies emib) []
  end.

(* Return all recursive dependencies in topological order of the specified seed declarations *)
Definition decl_deps_recursive
           (Σ : Ex.global_env)
           (seeds : list kername)
           (ignore : list kername) : option (list (kername * Ex.global_decl)) :=
  let fix go n seen name :=
      match n with
      | 0 => None
      | S n =>
        if (existsb (String.eqb name) ignore ||
            if Ex.lookup_env seen name then true else false)%bool then
          ret seen
        else
          match Ex.lookup_env Σ name with
          | Some decl =>
            let seen := (name, decl) :: seen in
            let deps := decl_deps decl in
            monad_fold_left (go n) deps seen
          | None =>
            None
          end
      end in
  monad_fold_left (go (N.to_nat 10000)) seeds [].

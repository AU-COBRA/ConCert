(* This implements a very rudimentary inlining pass without many heuristics.
   The pass is passed the name of definitions to be inlined and will inline
   beta, and iota reduce those definitions.

  Essentially, just an adaptaion of the inlining pass on the erased representation,
  plus proof genertion (proof by [reflexivity], since the terms before and after are convertible) *)
From ConCert.Extraction Require Import ExAst.
From ConCert.Extraction Require Import Transform.
From ConCert.Extraction Require Import Optimize.
From ConCert.Extraction Require Import ResultMonad.
From ConCert.Extraction Require Import Utils.
From MetaCoq.Erasure Require Import EAstUtils.
From MetaCoq.Erasure Require Import ELiftSubst.

Section inlining.
  Context (should_inline : kername -> bool).
  Context (Σ : global_env).

  Fixpoint beta_body (body : term) (args : list term) {struct args} : term :=
    match args with
    | [] => body
    | a :: args =>
      match body with
      | tLambda na body => beta_body (body{0 := a}) args
      | _ => mkApps (tApp body a) args
      end
    end.

  Definition iota_body (body : term) : term :=
    match body with
    | tCase (ind, pars) discr brs =>
      let (hd, args) := decompose_app discr in
      match hd with
      | tConstruct _ c =>
        match nth_error brs c with
        | Some (_, br) => beta_body br (skipn pars args)
        | None => body
        end
      | _ => body
      end
    | t => t
    end.

  Fixpoint inline_aux (args : list term) (t : term) : term :=
    match t with
    | tApp hd arg => inline_aux (inline_aux [] arg :: args) hd
    | tConst kn =>
      if should_inline kn then
        match lookup_env Σ kn with
        | Some (ConstantDecl cst) =>
          match cst_body cst with
          | Some body (* once told me *) =>
            (* Often the first beta will expose an iota (record projection),
               and the projected field is often a function, so we do another beta *)
            let (hd, args) := decompose_app (beta_body body args) in
            beta_body (iota_body hd) args
          | None => mkApps (tConst kn) args
          end
        | _ => mkApps (tConst kn) args
        end
      else
        mkApps (tConst kn) args
    | t => mkApps (map_subterms (inline_aux []) t) args
    end.

  Definition inline_in_constant_body cst :=
    {| cst_type := cst_type cst;
       cst_body := option_map (inline_aux []) (cst_body cst) |}.

  Definition inline_in_decl d :=
    match d with
    | ConstantDecl cst => ConstantDecl (inline_in_constant_body cst)
    | _ => d
    end.
End inlining.

Definition inline_in_env (should_inline : kername -> bool) (Σ : global_env) : global_env :=
  let newΣ := fold_right (fun '(kn, has_deps, decl) Σ =>
                           (kn, has_deps, inline_in_decl should_inline Σ decl) :: Σ)
                        [] Σ in
  filter (fun '(kn, _, _) => negb (should_inline kn)) newΣ.

Definition transform (should_inline : kername -> bool) : ExtractTransform :=
  fun Σ => Ok (timed "Inlining" (fun _ => inline_in_env should_inline Σ)).

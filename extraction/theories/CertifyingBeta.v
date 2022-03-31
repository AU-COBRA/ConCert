From Coq Require Import List.
From Coq Require Import String.
From ConCert.Extraction Require Import Transform.
From ConCert.Extraction Require Import Common.
From ConCert.Extraction Require Import ResultMonad.
From ConCert.Extraction Require Import Utils.
From ConCert.Extraction Require Import Certifying.
From MetaCoq.Template Require Import All.
From MetaCoq.Template Require Import Kernames.

Import MonadNotation.

Section betared.
  Context (Σ : global_env).

  Fixpoint decompose_lam (t : term) {struct t} :
  (list aname × list term) × term :=
    match t with
    | tLambda na A B =>
      let (nAs, B0) := decompose_lam B in
      let (ns, As) := nAs in (na :: ns, A :: As, B0)
    | _ => ([], [], t)
    end.

  Fixpoint betared_aux (args : list term) (t : term) : term :=
      match t with
      | tApp hd args0 => betared_aux (map (betared_aux []) args0 ++ args) hd
      | tCast t0 _ _ => betared_aux args t0
      | tLambda na ty body =>
        let b := betared_aux [] body in
        beta_body (tLambda na ty b) args
      | t => mkApps (map_subterms (betared_aux []) t) args
      end.

  Definition betared : term -> term := betared_aux [].

  Definition betared_in_constant_body cst :=
    {| cst_type := cst_type cst;
       cst_universes := cst_universes cst;
       cst_body := option_map betared (cst_body cst) |}.

  Definition betared_in_decl d :=
    match d with
    | ConstantDecl cst => ConstantDecl (betared_in_constant_body cst)
    | _ => d
    end.

End betared.

Definition betared_in_env (Σ : global_env) : global_env :=
  fold_right (fun '(kn, decl) Σ => (kn, betared_in_decl decl) :: Σ) [] Σ.

Definition betared_global_env_template
           (mpath : modpath)
           (Σ : global_env)
           (seeds : KernameSet.t)
  : TemplateMonad global_env :=
  let suffix := "_after_betared" in
  Σinlined <- tmEval lazy (betared_in_env Σ);;
  gen_defs_and_proofs Σ Σinlined mpath suffix seeds;;
  ret Σinlined.

(* Mainly for testing purposes *)
Definition betared_def {A}
           (def : A) : TemplateMonad _ :=
  mpath <- tmCurrentModPath tt;;
  p <- tmQuoteRecTransp def false ;;
  kn <- Common.extract_def_name def ;;
  betared_global_env_template mpath p.1 (KernameSet.singleton kn).


Definition template_betared : TemplateTransform :=
  fun Σ => Ok (timed "Inlining" (fun _ => betared_in_env Σ)).

Module Ex1.

  Definition foo (n : nat) := (fun x => x) n.

  MetaCoq Run (betared_def foo).

  MetaCoq Quote Recursively Definition foo_after :=
    ConCert_Extraction_CertifyingBeta_Ex1_foo_after_betared.

  MetaCoq Quote Recursively Definition foo_before := foo.

  Lemma after_not_before :
    lookup_env foo_after.1 <%% ConCert_Extraction_CertifyingBeta_Ex1_foo_after_betared %%> =
    lookup_env foo_before.1 <%% foo %%> -> False.
  Proof. easy. Qed.
End Ex1.

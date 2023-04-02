(** * Well-formedness conditions *)
From MetaCoq.Utils Require Import utils.
From ConCert.Embedding Require Import Ast.
From ConCert.Embedding Require Import EnvSubst.
From ConCert.Embedding Require Import EvalE.
From ConCert.Utils Require Import Env.

Import NamelessSubst.

Definition is_type e : bool :=
  match expr_to_ty e with
  | Some _ => true
  | _ => false
  end.

(** ** Well-formed global environment (In the paper: (WF.i)) *)

(** Well-formed constructor in the definition of an inductive *)
Definition constr_ok (nparam : nat) (c : constr) : bool :=
  forallb (iclosed_ty nparam) (map snd c.2).

(** Well-formed global declarations *)
Definition global_dec_ok (gd : global_dec) : bool :=
  match gd with
  | gdInd _ nparam cs _ => forallb (constr_ok nparam) cs
  end.

(** Well-formed global environment *)
Definition genv_ok Σ := forallb global_dec_ok Σ.


(** Well-formedness condition on evaluation environments wrt. a type:
    [ρ] is well-formed wrt. a type [ty] when for any type variables mentioned
    in [ty], if there is a corresponding expression in ρ (starting from the
    index [n]) it corresponds to a type. *)
  Fixpoint ty_env_ok (n : nat) (ρ : env expr) (ty : type): bool :=
    match ty with
    | tyInd x => true
    | tyForall v ty0 => ty_env_ok (S n) ρ ty0
    | tyApp ty1 ty2 => ty_env_ok n ρ ty1 && ty_env_ok n ρ ty2
    | tyVar _ => false
    | tyRel i => if Nat.leb n i then
                  match lookup_i ρ (i-n) with
                  (* if there is somethig in [ρ], it must be a type *)
                  | Some e => is_type e
                  (* if nothing there, that's ok *)
                  | None => true
                  end
                else true
    | tyArr ty1 ty2 => ty_env_ok n ρ ty1 && ty_env_ok n ρ ty2
    end.

  (** ** Well-formedness condition on evaluation environments wrt.
      an expression (In the paper : (WF.ii)) *)

  (** [ρ] is well-formed wrt. an expression [e] when for any type
      variables mentioned in [e], if there is a corresponding expression
      in ρ (starting from the index [n]) it corresponds to a type. *)

  Definition ty_expr_env_ok (ρ : env expr) : nat -> expr -> bool :=
    fix rec n e :=
      match e with
      | eRel i => true
      | eVar nm => false
      | eLambda nm ty b => ty_env_ok n ρ ty && rec (1+n) b
      | eTyLam nm b => rec (1+n) b
      | eLetIn nm e1 ty e2 => rec n e1 && ty_env_ok n ρ ty && rec (1+n) e2
      | eApp e1 e2 => rec n e1 && rec n e2
      | eConstr t i as e' => true
      | eConst nm => true
      | eCase nm_i ty e bs =>
        let bs'' := List.forallb
                      (fun x => rec (length (pVars (fst x)) + n) (snd x)) bs in
        forallb (ty_env_ok n ρ) (snd nm_i) && ty_env_ok n ρ ty && rec n e && bs''
      | eFix nm v ty1 ty2 b => ty_env_ok n ρ ty1 && ty_env_ok n ρ ty2 && rec (2+n) b
      | eTy ty => ty_env_ok n ρ ty
      end.

  (** This predicate defines a subset of types which are values *)
  Inductive ty_val : type -> Type :=
  | vtyInd : forall ind, ty_val (tyInd ind)
  | vtyRel : forall i, ty_val (tyRel i)
  | vtyForall : forall nm ty , ty_val ty -> ty_val (tyForall nm ty)
  | vtyApp : forall ty1 ty2 ind tys,
      decompose_inductive ty1 = Some (ind, tys) ->
      ty_val ty1 ->
      ty_val ty2 ->
      ty_val (tyApp ty1 ty2)
  | vtyArr : forall ty1 ty2,
      ty_val ty1 ->
      ty_val ty2 ->
      ty_val (tyArr ty1 ty2).

 (** Well-formed value (In the paper: (WF.iii)) *)
 Inductive val_ok Σ : val -> Type :=
  | vokClosLam : forall e nm ρ ty1 ty2,
      AllEnv (val_ok Σ) ρ ->
      ty_expr_env_ok (exprs ρ) 1 e ->
      iclosed_n (1 + length ρ) e ->
      iclosed_ty 0 ty1 ->
      iclosed_ty 0 ty2 ->
      ty_val ty1 ->
      ty_val ty2 ->
      val_ok Σ (vClos ρ nm cmLam ty1 ty2 e)
  | vokClosFix : forall e nm fixename ρ ty1 ty2,
      AllEnv (val_ok Σ) ρ ->
      ty_expr_env_ok (exprs ρ) 2 e ->
      iclosed_n (2 + length ρ) e ->
      iclosed_ty 0 ty1 ->
      iclosed_ty 0 ty2 ->
      ty_val ty1 ->
      ty_val ty2 ->
      val_ok Σ (vClos ρ nm (cmFix fixename) ty1 ty2 e)
  | vokTyClos : forall e nm ρ,
      AllEnv (val_ok Σ) ρ ->
      ty_expr_env_ok (exprs ρ) 1 e ->
      iclosed_n (1 + length ρ) e ->
      val_ok Σ (vTyClos ρ nm e)
  | vokContr : forall i nm vs ci,
      All (val_ok Σ) vs ->
      resolve_constr Σ i nm = Some ci ->
      #|vs| <= ci.1.1 + #|ci.2| ->
      val_ok Σ (vConstr i nm vs)
  | vokTy : forall ty,
      iclosed_ty 0 ty ->
      ty_val ty ->
      val_ok Σ (vTy ty).

 (** Well-formed evaluation environment contains well-formed values *)
 Definition env_ok Σ (ρ : env val) := AllEnv (val_ok Σ) ρ.

From ConCert.Extraction Require Import Erasure.
From ConCert.Extraction Require Import ExAst.
From ConCert.Extraction Require Import ExTyping.
From ConCert.Extraction Require Import StringExtra.
From ConCert.Extraction Require Import ResultMonad.
From Coq Require Import Arith.
From Coq Require Import Ascii.
From Coq Require Import Bool.
From Coq Require Import List.
From Coq Require Import PArith.
From Coq Require Import Psatz.
From Coq Require Import String.
From Coq Require VectorDef.
From Equations Require Import Equations.
From MetaCoq.Erasure Require Import EArities.
From MetaCoq.Erasure Require Import EAstUtils.
From MetaCoq.Erasure Require Import EInduction.
From MetaCoq.Erasure Require Import ELiftSubst.
From MetaCoq.Erasure Require Import Extract.
From MetaCoq.Erasure Require Import EWcbvEval.
From MetaCoq.Erasure Require Import Prelim.
From MetaCoq.Erasure Require SafeErasureFunction.
From MetaCoq.Template Require Import config.
From MetaCoq.Template Require Import monad_utils.
From MetaCoq.Template Require Import utils.
From MetaCoq Require Import PCUICGeneration.

Local Open Scope string_scope.
Import ListNotations.
Import MonadNotation.
Set Equations Transparent.

Import EAstUtils.
Import Erasure.
Import ExAst.

Definition map_subterms (f : term -> term) (t : term) : term :=
  match t with
  | tEvar n ts => tEvar n (map f ts)
  | tLambda na body => tLambda na (f body)
  | tLetIn na val body => tLetIn na (f val) (f body)
  | tApp hd arg => tApp (f hd) (f arg)
  | tCase p disc brs =>
    tCase p (f disc) (map (on_snd f) brs)
  | tProj p t => tProj p (f t)
  | tFix def i => tFix (map (map_def f) def) i
  | tCoFix def i => tCoFix (map (map_def f) def) i
  | t => t
  end.

Definition bitmask := list bool.

Fixpoint set_bit (n : nat) (bs : bitmask) : bitmask :=
  match n, bs with
  | 0, _ :: bs => true :: bs
  | 0, [] => [true]
  | S n, b :: bs => b :: set_bit n bs
  | S n, [] => false :: set_bit n []
  end.

Definition has_bit (n : nat) (bs : bitmask) : bool :=
  nth n bs false.

Definition bitmask_not (bs : bitmask) : bitmask :=
  map negb bs.

Definition count_zeros (bs : bitmask) : nat :=
  List.length (filter negb bs).

Fixpoint bitmask_or (bs1 bs2 : bitmask) : bitmask :=
  match bs1, bs2 with
  | b1 :: bs1, b2 :: bs2 => (b1 || b2) :: bitmask_or bs1 bs2
  | [], bs2 => bs2
  | bs1, [] => bs1
  end.

Notation "bs #|| bs'" := (bitmask_or bs bs') (at level 50, left associativity).

Definition trim_start (b : bool) : bitmask -> bitmask :=
  fix f bs :=
    match bs with
    | b' :: bs => if Bool.eqb b' b then
                    f bs
                  else
                    b' :: bs
    | [] => []
    end.

Definition trim_end (b : bool) (bs : bitmask) : bitmask :=
  List.rev (trim_start b (List.rev bs)).

Section dearg.
Record mib_masks := {
  (* Bitmask specifying which parameters to remove *)
  param_mask : bitmask;
  (* Bitmask specifying which **non-parameter** data to remove from
     each constructor. The full mask used for each constructor is the
     concatenation of the param_mask and this mask *)
  ctor_masks : list (nat * nat * bitmask); }.

Context (ind_masks : list (kername * mib_masks)).
Context (const_masks : list (kername * bitmask)).

Definition get_mib_masks (kn : kername) : option mib_masks :=
  option_map snd (find (fun '(kn', _) => eq_kername kn' kn) ind_masks).

Fixpoint dearg_single (mask : bitmask) (t : term) (args : list term) : term :=
  match mask, args with
  | true :: mask, arg :: args => dearg_single mask t args
  | false :: mask, arg :: args => dearg_single mask (tApp t arg) args
  | true :: mask, [] => tLambda nAnon (dearg_single mask (lift0 1 t) [])
  | false :: mask, [] => tLambda nAnon (dearg_single mask (tApp (lift0 1 t) (tRel 0)) [])
  | [], _ => mkApps t args
  end.

Definition get_ctor_mask (ind : inductive) (c : nat) : bitmask :=
  match get_mib_masks (inductive_mind ind) with
  | Some mib_masks =>
    let ctor_mask :=
        match find (fun '(ind', c', _) => (ind' =? inductive_ind ind) && (c' =? c))
                   (ctor_masks mib_masks) with
        | Some (_, _, ctor_mask) => ctor_mask
        | None => []
        end in
    param_mask mib_masks ++ ctor_mask
  | None => []
  end.

Definition get_const_mask (kn : kername) : bitmask :=
  match find (fun '(kn', _) => eq_kername kn' kn) const_masks with
  | Some (_, mask) => mask
  | None => []
  end.

Fixpoint dearg_lambdas (mask : bitmask) (ar : nat) (t : term) : nat * term :=
  match mask, t with
  | true :: mask, tLambda na body => dearg_lambdas mask (ar - 1) (body { 0 := tBox })
  | false :: mask, tLambda na body =>
    let (ar, t) := dearg_lambdas mask ar body in
    (ar, tLambda na t)
  | _, _ => (ar, t)
  end.

Definition dearg_case
           (ind : inductive)
           (npars : nat)
           (discr : term)
           (brs : list (nat * term)) : term :=
  match get_mib_masks (inductive_mind ind) with
  | Some mib_masks =>
    let new_npars := count_zeros (param_mask mib_masks) in
    let dearg_one c br :=
        match find (fun '(ind', c', _) => (ind' =? inductive_ind ind) && (c' =? c))
                   (ctor_masks mib_masks) with
        | Some (_, _, ctor_masks) => dearg_lambdas ctor_masks br.1 br.2
        | None => br
        end in
    tCase (ind, new_npars) discr (mapi dearg_one brs)
  | None => tCase (ind, npars) discr brs
  end.

Fixpoint dearg_aux (args : list term) (t : term) : term :=
  match t with
  | tApp hd arg => dearg_aux (dearg_aux [] arg :: args) hd
  | tConstruct ind c => dearg_single (get_ctor_mask ind c) t args
  | tConst kn => dearg_single (get_const_mask kn) t args
  | tCase (ind, npars) discr brs =>
    let discr := dearg_aux [] discr in
    let brs := map (on_snd (dearg_aux [])) brs in
    mkApps (dearg_case ind npars discr brs) args
  | t => mkApps (map_subterms (dearg_aux []) t) args
  end.

Definition dearg (t : term) : term :=
  dearg_aux [] t.

(* Remove lambda abstractions from top level declaration based on bitmask *)
Fixpoint dearg_cst_body_top (mask : bitmask) (body : term) : term :=
  match body with
  | tLetIn na val body => tLetIn na val (dearg_cst_body_top mask body)
  | tLambda na lam_body =>
    match mask with
    | true :: mask => (dearg_cst_body_top mask lam_body) { 0 := tBox }
    | false :: mask => tLambda na (dearg_cst_body_top mask lam_body)
    | [] => body
    end
  | _ => body
  end.

Fixpoint dearg_cst_type_top (mask : bitmask) (type : box_type) : box_type :=
  match mask, type with
  | true :: mask, TArr _ cod => dearg_cst_type_top mask cod
  | false :: mask, TArr dom cod => TArr dom (dearg_cst_type_top mask cod)
  | _, _ => type
  end.

(* Remove lambda abstractions from top level declaration and remove
   all unused args in applicacations *)
Definition dearg_cst (kn : kername) (cst : constant_body) : constant_body :=
  let mask := get_const_mask kn in
  {| cst_type := on_snd (dearg_cst_type_top mask) (cst_type cst);
     cst_body := option_map (dearg ∘ dearg_cst_body_top mask) (cst_body cst) |}.

(* Remove all data from ctor based on bitmask *)
Fixpoint dearg_oib_ctor (mask : bitmask) (bts : list box_type) : list box_type :=
  match mask, bts with
  | false :: mask, bt :: bts => bt :: dearg_oib_ctor mask bts
  | true :: mask, bt :: bts => dearg_oib_ctor mask bts
  | _, _ => bts
  end.

Definition dearg_oib
           (mib_masks : mib_masks)
           (oib_index : nat)
           (oib : one_inductive_body) : one_inductive_body :=
  {| ind_name := ind_name oib;
     ind_type_vars := ind_type_vars oib;
     ind_ctors :=
       mapi (fun c '(name, bts) =>
               let ctor_mask :=
                   match find (fun '(ind', c', _) => (ind' =? oib_index) && (c' =? c))
                              (ctor_masks mib_masks) with
                   | Some (_, _, mask) => mask
                   | None => []
                   end in
               (name, dearg_oib_ctor (param_mask mib_masks ++ ctor_mask) bts))
            (ind_ctors oib);
     ind_projs := ind_projs oib |}.

Definition dearg_mib (kn : kername) (mib : mutual_inductive_body) : mutual_inductive_body :=
  match get_mib_masks kn with
  | Some mib_masks =>
    {| ind_npars := count_zeros (param_mask mib_masks);
       ind_bodies := mapi (dearg_oib mib_masks) (ind_bodies mib) |}
  | None => mib
  end.

Definition dearg_decl (kn : kername) (decl : global_decl) : global_decl :=
  match decl with
  | ConstantDecl cst => ConstantDecl (dearg_cst kn cst)
  | InductiveDecl mib => InductiveDecl (dearg_mib kn mib)
  end.

Definition dearg_env (Σ : global_env) : global_env :=
  map (fun '(kn, decl) => (kn, dearg_decl kn decl)) Σ.

End dearg.

(* Return bitmask indicating which context variables have uses *)
Fixpoint used_context_vars (Γ : bitmask) (t : term) : bitmask :=
  match t with
  | tBox => Γ
  | tRel i => set_bit i Γ
  | tVar n => Γ
  | tEvar _ ts => fold_right bitmask_or Γ (map (used_context_vars Γ) ts)
  | tLambda _ cod => tl (used_context_vars (false :: Γ) cod)
  | tLetIn _ val body => tl (used_context_vars (false :: used_context_vars Γ val) body)
  | tApp hd arg => used_context_vars (used_context_vars Γ hd) arg
  | tConst _ => Γ
  | tConstruct _ _ => Γ
  | tCase _ disc brs =>
    let Γ := used_context_vars Γ disc in
    fold_right bitmask_or Γ (map (used_context_vars Γ ∘ snd) brs)
  | tProj _ t => used_context_vars Γ t
  | tFix defs _
  | tCoFix defs _ =>
    let Γfix := List.repeat false #|defs| ++ Γ in
    let Γfix := fold_right bitmask_or Γfix (map (used_context_vars Γfix ∘ dbody) defs) in
    skipn #|defs| Γfix
  end.

(* Return bitmask indicating which parameters are used by the
specified lambda abstractions. All parameters after the end of
the bit mask should be assumed to be used. *)
Fixpoint func_body_used_params (Γ : bitmask) (t : term) (ty : box_type) : bitmask * bitmask :=
  match t, ty with
  | tLetIn na val body, _ =>
    let Γ := used_context_vars Γ val in
    let (mask, Γ) := func_body_used_params (false :: Γ) body ty in
    (mask, tl Γ)
  | tLambda na body, TArr _ dom =>
    let (mask, Γ) := func_body_used_params (false :: Γ) body dom in
    (hd false Γ :: mask, tl Γ)
  | t, ty => ([], used_context_vars Γ t)
  end.

Definition constant_used_params (cst : constant_body) : bitmask :=
  match cst_body cst with
  | None => []
  | Some body => (func_body_used_params [] body (cst_type cst).2).1
  end.

Definition dearg_box_type (bt : box_type) : bool :=
  match bt with
  | TBox
  | TAny => true
  | _ => false
  end.

Definition make_dearg_mib_masks (mib : mutual_inductive_body) : mib_masks :=
  let par_mask := List.repeat true (ind_npars mib) in
  {| param_mask := par_mask;
     ctor_masks :=
       List.concat
         (mapi
            (fun i oib =>
               mapi (fun c '(name, bts) => (i, c, map dearg_box_type (skipn (ind_npars mib) bts)))
                    (ind_ctors oib))
            (ind_bodies mib)) |}.

Record dearg_set := {
  const_masks : list (kername * bitmask);
  ind_masks : list (kername * mib_masks); }.

(* Return a dearg set that will dearg all unused arguments (including parameters) *)
Fixpoint get_dearg_set_for_unused_args (Σ : global_env) : dearg_set :=
  match Σ with
  | [] => {| const_masks := []; ind_masks := [] |}
  | (kn, decl) :: Σ =>
    let (consts, inds) := get_dearg_set_for_unused_args Σ in
    let (consts, inds) :=
        match decl with
        | ConstantDecl cst => ((kn, bitmask_not (constant_used_params cst)) :: consts, inds)
        | InductiveDecl mib => (consts, (kn, make_dearg_mib_masks mib) :: inds)
        end in
    {| const_masks := consts; ind_masks := inds |}
  end.

(* Remove trailing "false" bits in masks in dearg set *)
Definition trim_dearg_set (ds : dearg_set) : dearg_set :=
  let dearg_mib_masks mm :=
      {| param_mask := param_mask mm; (* todo: we could trim this too
                                         if there are no ctor masks left *)
         ctor_masks := map (fun '(ind, c, mask) =>
                              (ind, c, trim_end false mask))
                           (ctor_masks mm) |} in
  {| const_masks := map (on_snd (trim_end false)) (const_masks ds);
     ind_masks := map (on_snd dearg_mib_masks) (ind_masks ds) |}.

Definition remove_unused_args (Σ : global_env) : global_env :=
  let ds := get_dearg_set_for_unused_args Σ in
  let ds := trim_dearg_set ds in
  dearg_env (ind_masks ds) (const_masks ds) Σ.

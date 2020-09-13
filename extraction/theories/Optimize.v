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

Definition has_bit (n : nat) (bs : bitmask) : bool :=
  nth n bs false.

Definition bitmask_not (bs : bitmask) : bitmask :=
  map negb bs.

Definition count_zeros (bs : bitmask) : nat :=
  List.length (filter negb bs).

Definition count_ones (bs : bitmask) : nat :=
  List.length (filter id bs).

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

(* Get the branch for a branch of an inductive, i.e. without including parameters of the inductive *)
Definition get_branch_mask (mm : mib_masks) (ind : inductive) (c : nat) : bitmask :=
  match find (fun '(ind', c', _) => (ind' =? inductive_ind ind) && (c' =? c))
             (ctor_masks mm) with
  | Some (_, _, mask) => mask
  | None => []
  end.

(* Get mask for a constructor, i.e. combined parameter and branch mask *)
Definition get_ctor_mask (ind : inductive) (c : nat) : bitmask :=
  match get_mib_masks (inductive_mind ind) with
  | Some mm => param_mask mm ++ get_branch_mask mm ind c
  | None => []
  end.

Definition get_const_mask (kn : kername) : bitmask :=
  match find (fun '(kn', _) => eq_kername kn' kn) const_masks with
  | Some (_, mask) => mask
  | None => []
  end.

(* Remove lambda abstractions based on bitmask *)
Fixpoint dearg_lambdas (mask : bitmask) (body : term) : term :=
  match body with
  | tLetIn na val body => tLetIn na val (dearg_lambdas mask body)
  | tLambda na lam_body =>
    match mask with
    | true :: mask => (dearg_lambdas mask lam_body) { 0 := tBox }
    | false :: mask => tLambda na (dearg_lambdas mask lam_body)
    | [] => body
    end
  | _ => body
  end.

Definition dearged_npars (mm : option mib_masks) (npars : nat) : nat :=
  match mm with
  | Some mm => count_zeros (param_mask mm)
  | None => npars
  end.

Definition dearg_case_branch
           (mm : mib_masks) (ind : inductive) (c : nat)
           (br : nat × term) : nat × term :=
  let mask := get_branch_mask mm ind c in
  (br.1 - count_ones mask, dearg_lambdas mask br.2).

Definition dearg_case_branches
           (mm : option mib_masks)
           (ind : inductive)
           (brs : list (nat × term)) :=
  match mm with
  | Some mm => mapi (dearg_case_branch mm ind) brs
  | None => brs
  end.

Definition dearged_proj_arg (mm : option mib_masks) (ind : inductive) (arg : nat) : nat :=
  match mm with
  | Some mm => let mask := get_branch_mask mm ind 0 in
               arg - count_ones (firstn arg mask)
  | None => arg
  end.

Definition dearg_case
           (ind : inductive)
           (npars : nat)
           (discr : term)
           (brs : list (nat * term)) : term :=
  let mm := get_mib_masks (inductive_mind ind) in
  tCase (ind, dearged_npars mm npars) discr (dearg_case_branches mm ind brs).

Definition dearg_proj (ind : inductive) (npars arg : nat) (discr : term) : term :=
  let mm := get_mib_masks (inductive_mind ind) in
  tProj (ind, dearged_npars mm npars, dearged_proj_arg mm ind arg) discr.

Fixpoint dearg_aux (args : list term) (t : term) : term :=
  match t with
  | tApp hd arg => dearg_aux (dearg_aux [] arg :: args) hd
  | tConstruct ind c => dearg_single (get_ctor_mask ind c) t args
  | tConst kn => dearg_single (get_const_mask kn) t args
  | tCase (ind, npars) discr brs =>
    let discr := dearg_aux [] discr in
    let brs := map (on_snd (dearg_aux [])) brs in
    mkApps (dearg_case ind npars discr brs) args
  | tProj (ind, npars, arg) t =>
    mkApps (dearg_proj ind npars arg (dearg_aux [] t)) args
  | t => mkApps (map_subterms (dearg_aux []) t) args
  end.

Definition dearg (t : term) : term :=
  dearg_aux [] t.

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
     cst_body := option_map (dearg ∘ dearg_lambdas mask) (cst_body cst) |}.

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
     ind_ctor_type_vars := ind_ctor_type_vars oib;
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
  | InductiveDecl b mib => InductiveDecl b (dearg_mib kn mib)
  | TypeAliasDecl _ => decl
  end.

Definition dearg_env (Σ : global_env) : global_env :=
  map (fun '(kn, decl) => (kn, dearg_decl kn decl)) Σ.

End dearg.

Fixpoint clear_bit (n : nat) (bs : bitmask) : bitmask :=
  match n, bs with
  | 0, _ :: bs => false :: bs
  | S n, b :: bs => b :: clear_bit n bs
  | _, _ => []
  end.

(* Return bitmask indicating which context variables are dead, i.e. unused. *)
Fixpoint dead_context_vars (Γ : bitmask) (t : term) : bitmask :=
  match t with
  | tBox => Γ
  | tRel i => clear_bit i Γ
  | tVar n => Γ
  | tEvar _ ts => fold_right (fun t Γ => dead_context_vars Γ t) Γ ts
  | tLambda _ cod => tl (dead_context_vars (true :: Γ) cod)
  | tLetIn _ val body => tl (dead_context_vars (true :: dead_context_vars Γ val) body)
  | tApp hd arg => dead_context_vars (dead_context_vars Γ hd) arg
  | tConst _ => Γ
  | tConstruct _ _ => Γ
  | tCase _ disc brs =>
    let Γ := dead_context_vars Γ disc in
    fold_right (fun br Γ => dead_context_vars Γ br.2) Γ brs
  | tProj _ t => dead_context_vars Γ t
  | tFix defs _
  | tCoFix defs _ =>
    let Γ := List.repeat false #|defs| ++ Γ in
    let Γ := fold_right (fun d Γ => dead_context_vars Γ (dbody d)) Γ defs in
    skipn #|defs| Γ
  end.

(* Return bitmask indicating which parameters are dead in the
specified lambda abstractions. All parameters after the end of
the bit mask should be assumed to be live. *)
Fixpoint func_body_dead_params (Γ : bitmask) (t : term) (ty : box_type) : bitmask * bitmask :=
  match t, ty with
  | tLetIn na val body, _ =>
    let Γ := dead_context_vars Γ val in
    let (mask, Γ) := func_body_dead_params (true :: Γ) body ty in
    (mask, tl Γ)
  | tLambda na body, TArr _ dom =>
    let (mask, Γ) := func_body_dead_params (true :: Γ) body dom in
    (hd false Γ :: mask, tl Γ)
  | t, ty => ([], dead_context_vars Γ t)
  end.

Definition constant_dead_params (cst : constant_body) : bitmask :=
  match cst_body cst with
  | None => []
  | Some body => (func_body_dead_params [] body (cst_type cst).2).1
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
        | ConstantDecl cst => ((kn, constant_dead_params cst) :: consts, inds)
        | InductiveDecl _ mib => (consts, (kn, make_dearg_mib_masks mib) :: inds)
        | TypeAliasDecl _ =>
          (* FIXME: look for unused parameters in type alisases? *)
          (consts,inds)
        end in
    {| const_masks := consts; ind_masks := inds |}
  end.

(* Remove trailing "false" bits in masks in dearg set *)
Definition trim_dearg_set (ds : dearg_set) : dearg_set :=
  let dearg_mib_masks mm :=
      {| param_mask := param_mask mm;
         ctor_masks := map (fun '(ind, c, mask) =>
                              (ind, c, trim_end false mask))
                           (ctor_masks mm) |} in
  {| const_masks := map (on_snd (trim_end false)) (const_masks ds);
     ind_masks := map (on_snd dearg_mib_masks) (ind_masks ds) |}.

Definition remove_unused_args (Σ : global_env) : global_env :=
  let ds := get_dearg_set_for_unused_args Σ in
  let ds := trim_dearg_set ds in
  dearg_env (ind_masks ds) (const_masks ds) Σ.

Definition map_subterms_box_type (f : box_type -> box_type) (ty : box_type) : box_type :=
  match ty with
  | TArr dom codom => TArr (f dom) (f codom)
  | TApp ty1 ty2 => TApp (f ty1) (f ty2)
  | _ => ty
  end.

Fixpoint decompose_TApp (bt : box_type) : list box_type × box_type :=
  match bt with
  | TApp dom cod => let (args, res) := decompose_TApp cod in (dom :: args, res)
  | _ => ([], bt)
  end.

Fixpoint mkAppsBt (t : box_type) (us : list box_type) : box_type :=
  match us with
  | [] => t
  | a :: args => mkAppsBt (TApp t a) args
  end.

Fixpoint dearg_single_bt (mask : bitmask) (t : box_type) (args : list box_type)
  : box_type :=
  match mask, args with
  | true :: mask, arg :: args => dearg_single_bt mask t args
  | false :: mask, arg :: args => dearg_single_bt mask (TApp t arg) args
  | _, _ => mkAppsBt t args
  end.

Definition dearg_ty_const (const_masks : list (kername × bitmask)) (kn : kername)
           (args : list box_type) :=
  dearg_single_bt (get_const_mask const_masks kn) (TConst kn) args.

Definition get_param_mask (oib : one_inductive_body) : bitmask :=
  map (fun x => tvar_is_logical x || negb (tvar_is_sort x))
      oib.(ind_type_vars).

Definition get_ctor_param_mask (oib : one_inductive_body) : bitmask :=
  map (fun x => tvar_is_logical x || negb (tvar_is_sort x))
      oib.(ind_ctor_type_vars).

Definition dearg_ty_ind (ind_masks : list (inductive × bitmask))
           (ind : inductive)
           (args : list box_type) :=
  let kn := ind.(inductive_mind) in
  let i := ind.(inductive_ind) in
  let mask_o :=
      find (fun '(mkInd kn' i',_) => eq_kername kn' kn && Nat.eqb i i')
           ind_masks in
  match mask_o with
  | Some (_, mask) => dearg_single_bt mask (TInd ind) args
  | None => mkAppsBt (TInd ind) args
  end.

Record dearg_set_ty :=
  { dst_const_masks : list (kername × bitmask);
    dst_ind_masks : list (inductive × bitmask) }.

Definition get_tvar_shift (i : nat) (ind_par_mask : bitmask) : nat :=
  #|filter id (firstn i ind_par_mask)|.

Fixpoint debox_box_type_aux (ind_par_mask : bitmask)(ds : dearg_set_ty) (app_args : list box_type) (bt : box_type) : box_type :=
  match bt with
  | TArr dom codom =>
    match dom with
    | TBox => debox_box_type_aux ind_par_mask ds app_args codom (* we turn [box -> ty] into [ty] *)
    | TArr TBox codom' =>
      (* NOTE: we do not remove boxes in a negative position *)
      TArr (TArr TBox (debox_box_type_aux ind_par_mask ds app_args codom'))
           (debox_box_type_aux ind_par_mask ds app_args codom)
    | _ => TArr (debox_box_type_aux ind_par_mask ds app_args dom) (debox_box_type_aux ind_par_mask ds app_args codom)
    end
  | TApp ty1 ty2 =>
    debox_box_type_aux ind_par_mask ds (debox_box_type_aux ind_par_mask ds [] ty2 :: app_args) ty1
  | TInd ind => dearg_ty_ind ds.(dst_ind_masks) ind app_args
  | TConst kn => dearg_ty_const ds.(dst_const_masks) kn app_args
  | TVar i => TVar (i - get_tvar_shift i ind_par_mask)
  | TAny | TBox => bt
  end.

Definition debox_box_type (ind_par_mask : bitmask) (ds : dearg_set_ty) (bt : box_type) :=
  debox_box_type_aux ind_par_mask ds [] bt.

Fixpoint remove_logical_params_ctor (ind_par_mask : bitmask) (ds : dearg_set_ty) (ctor : ident × list box_type) : ident × list box_type
  := let '(nm,tys) := ctor in
     (nm, map (debox_box_type ind_par_mask ds) tys).

Definition remove_logical_params (ds : dearg_set_ty) (oib : ExAst.one_inductive_body) :=
  let mask := get_param_mask oib in
  let mask_ctor := get_ctor_param_mask oib in
  let filtered_ty_vars :=
      map snd (filter (negb ∘ fst) (combine mask oib.(ind_type_vars))) in
    let filtered_ctor_ty_vars :=
        map snd (filter (negb ∘ fst) (combine mask_ctor oib.(ind_ctor_type_vars))) in
  {| ind_name:= oib.(ind_name);
     ind_type_vars := filtered_ty_vars;
     ind_ctor_type_vars := filtered_ctor_ty_vars;
     ind_ctors := map (remove_logical_params_ctor mask_ctor ds) oib.(ind_ctors);
     ind_projs := oib.(ind_projs) |}.

Fixpoint get_param_masks_global_env (Σ : ExAst.global_env)
  : list (inductive * bitmask) :=
  match Σ with
  | (kn, InductiveDecl _ mib) :: Σ' =>
    let get_for_mib kn mib :=
        mapi (fun i oib =>(mkInd kn i, get_param_mask oib)) mib.(ind_bodies) in
    get_for_mib kn mib ++ get_param_masks_global_env Σ'
  | _ :: Σ' => get_param_masks_global_env Σ'
  | [] => []
  end.

Definition remove_logical_params_mib (ds : dearg_set_ty) (ind : ExAst.mutual_inductive_body) :  ExAst.mutual_inductive_body :=
  {| ind_npars := ind.(ind_npars);
     ind_bodies :=
       map (remove_logical_params ds) ind.(ind_bodies) |}.

Definition debox_types_global_env (Σ : ExAst.global_env) : ExAst.global_env :=
  let _ds := get_dearg_set_for_unused_args Σ in
  let ind_masks := get_param_masks_global_env Σ in
  let ds := {| dst_const_masks := _ds.(const_masks);
               dst_ind_masks := ind_masks|} in
  map (on_snd
         (fun d => match d with
                | ConstantDecl cst =>
                  ConstantDecl {| cst_type := let '(nm,ty) := cst.(cst_type) in
                                              (nm, debox_box_type [] ds ty) ;
                                  cst_body := cst.(cst_body) |}
                | InductiveDecl b ind =>
                  InductiveDecl b (remove_logical_params_mib ds ind)
                | TypeAliasDecl (nms, ty) => TypeAliasDecl (nms, debox_box_type [] ds ty)
                end)) Σ.

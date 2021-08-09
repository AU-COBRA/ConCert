From ConCert.Extraction Require Import ClosedAux.
From ConCert.Extraction Require Import Erasure.
From ConCert.Extraction Require Import ExAst.
From ConCert.Extraction Require Import Transform.
From ConCert.Extraction Require Import ResultMonad.
From ConCert.Utils Require Import StringExtra.
From ConCert.Extraction Require Import Utils.
From Coq Require Import Arith.
From Coq Require Import Ascii.
From Coq Require Import Bool.
From Coq Require Import List.
From Coq Require Import PArith.
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
From MetaCoq.Erasure Require ErasureFunction.
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
  | _, _ => []
  end.

Fixpoint bitmask_and (bs1 bs2 : bitmask) : bitmask :=
  match bs1, bs2 with
  | b1 :: bs1, b2 :: bs2 => (b1 && b2) :: bitmask_and bs1 bs2
  | _, _ => []
  end.

Definition trim_start (b : bool) : bitmask -> bitmask :=
  fix f bs :=
    match bs with
    | b' :: bs =>
      if Bool.eqb b' b then
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

Fixpoint masked {X} (mask : bitmask) (xs : list X) :=
  match mask with
  | [] => xs
  | b :: mask =>
    match xs with
    | [] => []
    | x :: xs =>
      match b with
      | true => masked mask xs
      | false => x :: masked mask xs
      end
    end
  end.

Definition dearg_oib
           (mib_masks : mib_masks)
           (oib_index : nat)
           (oib : one_inductive_body) : one_inductive_body :=
  {| ind_name := ind_name oib;
     ind_propositional := ind_propositional oib;
     ind_kelim := ind_kelim oib;
     ind_type_vars := ind_type_vars oib;
     ind_ctors :=
       mapi (fun c '(name, fields) =>
               let ctor_mask :=
                   match find (fun '(ind', c', _) => (ind' =? oib_index) && (c' =? c))
                              (ctor_masks mib_masks) with
                   | Some (_, _, mask) => mask
                   | None => []
                   end in
               (name, masked (param_mask mib_masks ++ ctor_mask) fields))
            (ind_ctors oib);
     ind_ctor_original_arities := ind_ctor_original_arities oib;
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
  | TypeAliasDecl _ => decl
  end.

Definition dearg_env (Σ : global_env) : global_env :=
  map (fun '(kn, has_deps, decl) => (kn, has_deps, dearg_decl kn decl)) Σ.

(* Validity checks used when invoking the pass and to prove it correct *)
Fixpoint is_dead (rel : nat) (t : term) : bool :=
  match t with
  | tRel i => negb (i =? rel)
  | tEvar _ ts => forallb (is_dead rel) ts
  | tLambda _ body => is_dead (S rel) body
  | tLetIn _ val body => is_dead rel val && is_dead (S rel) body
  | tApp hd arg => is_dead rel hd && is_dead rel arg
  | tCase _ discr brs => is_dead rel discr && forallb (is_dead rel ∘ snd) brs
  | tProj _ t => is_dead rel t
  | tFix defs _
  | tCoFix defs _ => forallb (is_dead (#|defs| + rel) ∘ dbody) defs
  | _ => true
  end.

Fixpoint valid_dearg_mask (mask : bitmask) (body : term) : bool :=
  match body, mask with
  | tLetIn na val body, _ => valid_dearg_mask mask body
  | tLambda _ body, b :: mask =>
    (if b then is_dead 0 body else true) && valid_dearg_mask mask body
  | _, [] => true
  | _, _ => false
  end.

Definition valid_case_masks (ind : inductive) (npars : nat) (brs : list (nat * term)) : bool :=
  match get_mib_masks (inductive_mind ind) with
  | Some mm =>
    (#|param_mask mm| =? npars) &&
    alli (fun c '(ar, br) =>
            (#|get_branch_mask mm ind c| <=? ar) &&
            (valid_dearg_mask (get_branch_mask mm ind c) br)) brs 0
  | None => true
  end.

Definition valid_proj (ind : inductive) (npars arg : nat) : bool :=
  match get_mib_masks (inductive_mind ind) with
  | Some mm => (#|param_mask mm| =? npars) &&
               (* Projected argument must not be removed *)
               negb (nth arg (get_branch_mask mm ind 0) false)
  | _ => true
  end.

(* Check that all case and projections in a term are valid according
   to the masks. They must have the proper number of parameters, and
   1. For cases, their branches must be compatible with the masks,
      i.e. they are iterated lambdas/let-ins and when "true" appears in the mask,
      the parameter is unused
   2. For projections, the projected argument must not be removed *)
Fixpoint valid_cases (t : term) : bool :=
  match t with
  | tEvar _ ts => forallb valid_cases ts
  | tLambda _ body => valid_cases body
  | tLetIn _ val body => valid_cases val && valid_cases body
  | tApp hd arg => valid_cases hd && valid_cases arg
  | tCase (ind, npars) discr brs =>
    valid_cases discr && forallb (valid_cases ∘ snd) brs && valid_case_masks ind npars brs
  | tProj (ind, npars, arg) t => valid_cases t && valid_proj ind npars arg
  | tFix defs _
  | tCoFix defs _  => forallb (valid_cases ∘ dbody) defs
  | _ => true
  end.

Definition valid_masks_decl (p : kername * bool * global_decl) : bool :=
  match p with
  | (kn, _, ConstantDecl {| cst_body := Some body |}) =>
    valid_dearg_mask (get_const_mask kn) body && valid_cases body
  | (kn, _, TypeAliasDecl typ) => #|get_const_mask kn| =? 0
  | _ => true
  end.

(* Proposition representing whether masks are valid for entire environment.
   We should be able to prove that our analysis produces masks that satisfy this
   predicate. *)
Definition valid_masks_env (Σ : global_env) : bool :=
  forallb valid_masks_decl Σ.

(* Check if all applications are applied enough to be deboxed without eta expansion *)
Fixpoint is_expanded_aux (nargs : nat) (t : term) : bool :=
  match t with
  | tBox => true
  | tRel _ => true
  | tVar _ => true
  | tEvar _ ts => forallb (is_expanded_aux 0) ts
  | tLambda _ body => is_expanded_aux 0 body
  | tLetIn _ val body => is_expanded_aux 0 val && is_expanded_aux 0 body
  | tApp hd arg => is_expanded_aux 0 arg && is_expanded_aux (S nargs) hd
  | tConst kn => #|get_const_mask kn| <=? nargs
  | tConstruct ind c => #|get_ctor_mask ind c| <=? nargs
  | tCase _ discr brs => is_expanded_aux 0 discr && forallb (is_expanded_aux 0 ∘ snd) brs
  | tProj _ t => is_expanded_aux 0 t
  | tFix defs _
  | tCoFix defs _ => forallb (is_expanded_aux 0 ∘ dbody) defs
  | tPrim _ => true
  end.

(* Check if all applications are applied enough to be deboxed without eta expansion *)
Definition is_expanded (t : term) : bool :=
  is_expanded_aux 0 t.

(* Like above, but check all bodies in environment. This assumption does not necessarily hold,
   but we should try to make it hold by eta expansion before quoting *)
Definition is_expanded_env (Σ : global_env) : bool :=
  forallb (fun '(kn, decl) =>
             match decl with
             | ConstantDecl {| cst_body := Some body |} => is_expanded body
             | _ => true
             end) Σ.

End dearg.

Section dearg_types.
Context (Σ : global_env).

Definition keep_tvar tvar :=
  tvar_is_arity tvar && negb (tvar_is_logical tvar).

Fixpoint dearg_single_bt (tvars : list type_var_info) (t : box_type) (args : list box_type)
  : box_type :=
  match tvars, args with
  | tvar :: tvars, arg :: args =>
    if keep_tvar tvar then
      dearg_single_bt tvars (TApp t arg) args
    else
      dearg_single_bt tvars t args
  | _, _ => mkTApps t args
  end.

Definition get_inductive_tvars (ind : inductive) : list type_var_info :=
  match lookup_inductive Σ ind with
  | Some oib => ind_type_vars oib
  | None => []
  end.

Fixpoint debox_box_type_aux (args : list box_type) (bt : box_type) : box_type :=
  match bt with
  | TArr dom codom =>
    TArr (debox_box_type_aux [] dom) (debox_box_type_aux [] codom)
  | TApp ty1 ty2 =>
    debox_box_type_aux (debox_box_type_aux [] ty2 :: args) ty1
  | TInd ind => dearg_single_bt (get_inductive_tvars ind) bt args
  | TConst kn => match lookup_env Σ kn with
                | Some (TypeAliasDecl (Some (vs, ty))) =>
                  dearg_single_bt vs bt args
                | _ => bt
                end
  | _ => mkTApps bt args
  end.

Definition debox_box_type (bt : box_type) : box_type :=
  debox_box_type_aux [] bt.

Definition debox_type_constant (cst : constant_body) : constant_body :=
  {| cst_type := on_snd debox_box_type (cst_type cst);
     cst_body := cst_body cst; |}.

Definition reindex (tvars : list type_var_info) :=
  fix f (bt : box_type) : box_type :=
    match bt with
    | TArr dom cod => TArr (f dom) (f cod)
    | TApp hd arg => TApp (f hd) (f arg)
    | TVar i => TVar #|filter keep_tvar (firstn i tvars)|
    | _ => bt
    end.

Definition debox_type_oib (oib : one_inductive_body) : one_inductive_body :=
  let debox := reindex (ind_type_vars oib) ∘ debox_box_type in
  {| ind_name := ind_name oib;
     ind_propositional := ind_propositional oib;
     ind_kelim := ind_kelim oib;
     ind_type_vars := filter keep_tvar (ind_type_vars oib);
     ind_ctors := map (on_snd (map (on_snd debox))) (ind_ctors oib);
     ind_ctor_original_arities := ind_ctor_original_arities oib;
     ind_projs := map (on_snd debox) (ind_projs oib); |}.

Definition debox_type_mib (mib : mutual_inductive_body) : mutual_inductive_body :=
  {| ind_npars := ind_npars mib; ind_bodies := map debox_type_oib (ind_bodies mib) |}.

Definition debox_type_decl (decl : global_decl) : global_decl :=
  match decl with
  | ConstantDecl cst => ConstantDecl (debox_type_constant cst)
  | InductiveDecl mib => InductiveDecl (debox_type_mib mib)
  | TypeAliasDecl ta => match ta with
                       | Some (ty_vars, ty) =>
                         TypeAliasDecl (Some (filter keep_tvar ty_vars,
                                              reindex ty_vars (debox_box_type ty)))
                       | None => TypeAliasDecl None
                       end
  end.

End dearg_types.

Definition debox_env_types (Σ : global_env) : global_env :=
  map (on_snd (debox_type_decl Σ)) Σ.

Fixpoint clear_bit (n : nat) (bs : bitmask) : bitmask :=
  match n, bs with
  | 0, _ :: bs => false :: bs
  | S n, b :: bs => b :: clear_bit n bs
  | _, _ => []
  end.

(* Pair of bitmask and inductive masks.
   The first projection is a bitmask of dead local variables, i.e. when a use is found,
   a bit in this is set to false.
   The second projection is a list of dead constructor datas. When a use of a constructor
   parameter is found, this is set to false. *)
Definition analyze_state := bitmask × list (kername × mib_masks).

Definition set_used (s : analyze_state) (n : nat) : analyze_state :=
  (clear_bit n s.1, s.2).

Definition new_vars (s : analyze_state) (n : nat) : analyze_state :=
  (List.repeat true n ++ s.1, s.2).

Definition new_var (s : analyze_state) : analyze_state :=
  (true :: s.1, s.2).

Definition remove_vars (s : analyze_state) (n : nat) : analyze_state :=
  (skipn n s.1, s.2).

Definition remove_var (s : analyze_state) : analyze_state :=
  (tl s.1, s.2).

Definition update_mib_masks
           (s : analyze_state)
           (kn : kername)
           (mm : mib_masks) : analyze_state :=
  let fix update_list l :=
      match l with
      | [] => []
      | (kn', mm') :: l =>
        if eq_kername kn' kn then
          (kn, mm) :: l
        else
          (kn', mm') :: update_list l
      end in
  (s.1, update_list s.2).

Fixpoint update_ind_ctor_mask
         (ind : nat)
         (c : nat)
         (ctor_masks : list (nat * nat * bitmask))
         (f : bitmask -> bitmask) : list (nat * nat * bitmask) :=
  match ctor_masks with
  | [] => []
  | (ind', c', mask') :: ctor_masks =>
    if (ind' =? ind) && (c' =? c) then
      (ind', c', f mask') :: ctor_masks
    else
      (ind', c', mask') :: update_ind_ctor_mask ind c ctor_masks f
  end.

Definition fold_lefti {A B} (f : nat -> A -> B -> A) :=
  fix fold_lefti (n : nat) (l : list B) (a0 : A) :=
    match l with
    | [] => a0
    | b :: t => fold_lefti (S n) t (f n a0 b)
    end.

Section AnalyzeTop.
  Context (analyze : analyze_state -> term -> analyze_state).
  (* Analyze iterated let-in and lambdas to find dead variables inside body.
   Return bitmask of max length n indicating which lambda arguments are unused. *)
  Fixpoint analyze_top_level
           (state : analyze_state)
           (max_lams : nat)
           (t : term) {struct t} : bitmask × analyze_state :=
    match t, max_lams with
    | tLetIn na val body, _ =>
      let state := analyze state val in
      let (mask, state) := analyze_top_level (new_var state) max_lams body in
      (* Add nothing to mask *)
      (mask, remove_var state)
    | tLambda na body, S max_lams =>
      let (mask, state) := analyze_top_level (new_var state) max_lams body in
      (* Add to mask indicating whether this arg is unused *)
      (hd true state.1 :: mask, remove_var state)
    | t, _ => ([], analyze state t)
    end.
End AnalyzeTop.

Fixpoint analyze (state : analyze_state) (t : term) {struct t} : analyze_state :=
  match t with
  | tBox => state
  | tRel i => set_used state i
  | tVar n => state
  | tEvar _ ts => fold_left analyze ts state
  | tLambda _ cod => remove_var (analyze (new_var state) cod)
  | tLetIn _ val body => remove_var (analyze (new_var (analyze state val)) body)
  | tApp hd arg => analyze (analyze state hd) arg
  | tConst _ => state
  | tConstruct _ _ => state
  | tCase (ind, npars) discr brs =>
    let state := analyze state discr in
    match get_mib_masks state.2 (inductive_mind ind) with
    | Some mm =>
      let analyze_case c '(state, ctor_masks) brs :=
          let (mask, state) := analyze_top_level analyze state brs.1 brs.2 in
          (* If mask is too short it means the branch is not an iterated lambda.
           In this case we cannot know if the remaining args are dead, so pad
           with 0's *)
          let mask := mask ++ List.repeat false (brs.1 - #|mask|) in
          (state, update_ind_ctor_mask (inductive_ind ind) c ctor_masks (bitmask_and mask)) in
      let (state, ctor_masks) := fold_lefti analyze_case 0 brs (state, ctor_masks mm) in
      let mm := {| param_mask := param_mask mm; ctor_masks := ctor_masks |} in
      update_mib_masks state (inductive_mind ind) mm
    | None => state
    end
  | tProj (ind, npars, arg) t =>
    let state := analyze state t in
    match get_mib_masks state.2 (inductive_mind ind) with
    | Some mm =>
      let ctor_masks :=
          update_ind_ctor_mask (inductive_ind ind) 0 (ctor_masks mm) (clear_bit arg) in
      let mm := {| param_mask := param_mask mm; ctor_masks := ctor_masks |} in
      update_mib_masks state (inductive_mind ind) mm
    | None => state
    end
  | tFix defs _
  | tCoFix defs _ =>
    let state := new_vars state #|defs| in
    let state := fold_left (fun state d => analyze state (dbody d)) defs state in
    remove_vars state #|defs|
  | tPrim _ => state
  end.

Fixpoint decompose_TArr (bt : box_type) : list box_type × box_type :=
  match bt with
  | TArr dom cod => map_fst (cons dom) (decompose_TArr cod)
  | _ => ([], bt)
  end.

Definition is_box_or_any (bt : box_type) : bool :=
  match bt with
  | TBox
  | TAny => true
  | _ => false
  end.

Definition analyze_constant
           (cst : constant_body)
           (inds : list (kername × mib_masks)) : bitmask × list (kername × mib_masks) :=
  let '(doms, codom) := decompose_TArr (cst_type cst).2 in
  match cst_body cst with
  | Some body =>
    let max_lams := #|doms| in
    let '(mask, (_, inds)) := analyze_top_level analyze ([], inds) max_lams body in
    (* NOTE: if all the arguments are logical, we keep the first one in order to prevent contstans like [false_rect] to be evaluated eagerly in the extracted code *)
    if forallb is_box_or_any doms then
      (clear_bit 0 mask, inds)
    else (mask, inds)
  | None => (map is_box_or_any doms, inds)
  end.

Record dearg_set := {
  const_masks : list (kername * bitmask);
  ind_masks : list (kername * mib_masks); }.

Fixpoint analyze_env
         (overridden_masks : kername -> option bitmask)
         (Σ : global_env) : dearg_set :=
  match Σ with
  | [] => {| const_masks := []; ind_masks := [] |}
  | (kn, has_deps, decl) :: Σ =>
    let (consts, inds) := analyze_env overridden_masks Σ in
    let (consts, inds) :=
        match decl with
        | ConstantDecl cst =>
          let '(mask, inds) := analyze_constant cst inds in
          let mask := option_get mask (overridden_masks kn) in
          ((kn, mask) :: consts, inds)
        | InductiveDecl mib =>
          let ctor_masks :=
              List.concat
                (mapi (fun ind oib =>
                         mapi (fun c '(_, args) =>
                                 (ind, c, map (is_box_or_any ∘ snd)
                                              (skipn (ind_npars mib) args)))
                              (ind_ctors oib))
                      (ind_bodies mib)) in
          let mm := {| param_mask := List.repeat true (ind_npars mib);
                       ctor_masks := ctor_masks |} in
          (consts, (kn, mm) :: inds)
        | TypeAliasDecl _ => (consts, inds)
        end in
    {| const_masks := consts; ind_masks := inds |}
  end.

(* Remove trailing "false" bits in masks *)
Definition trim_const_masks (cm : list (kername × bitmask)) :=
  map (on_snd (trim_end false)) cm.

Definition trim_ctor_masks (cm : list ((nat × nat) × bitmask)) :=
  map (fun '(ind, c, mask) => (ind, c, trim_end false mask)) cm.

Definition trim_mib_masks (mm : mib_masks) :=
  {| param_mask := param_mask mm;
     ctor_masks := trim_ctor_masks (ctor_masks mm) |}.

Definition trim_ind_masks (im : list (kername × mib_masks)) :=
  map (on_snd trim_mib_masks) im.

Definition dearg_transform
           (overridden_masks : kername -> option bitmask)
           (* If true, trim ends of constant masks to avoid unnecessary eta expansion. *)
           (do_trim_const_masks : bool)
           (* If true, trim ends of constructor masks to avoid unnecessary eta expansion. *)
           (do_trim_ctor_masks : bool)
           (* Check if erased environment is closed *)
           (check_closed : bool)
           (* Check that environment is expanded enough before dearging *)
           (check_expanded : bool)
           (* Check that the dearg masks generated by analysis are valid for dearging *)
           (check_valid_masks : bool) : ExtractTransform :=
  fun Σ =>
    (if check_closed && negb (env_closed (trans_env Σ)) then
       Err "Erased environment is not closed"
     else
       Ok tt);;

    let (const_masks, ind_masks) := timed "Dearg analysis"
                                          (fun _ => analyze_env overridden_masks Σ) in

    let const_masks := (if do_trim_const_masks then trim_const_masks else id) const_masks in
    let ind_masks := (if do_trim_ctor_masks then trim_ind_masks else id) ind_masks in

    (if check_expanded && negb (is_expanded_env ind_masks const_masks Σ) then
       Err "Erased environment is not expanded enough for dearging to be provably correct"
     else
       Ok tt);;

    (if check_valid_masks && negb (valid_masks_env ind_masks const_masks Σ) then
       Err "Analysis produced masks that ask to remove live arguments"
     else
       Ok tt);;

    ret (debox_env_types (timed "Dearging" (fun _ => dearg_env ind_masks const_masks Σ))).

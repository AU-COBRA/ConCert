From ConCert.Extraction Require Import Aux.
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
               (name, masked (param_mask mib_masks ++ ctor_mask) bts))
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

Section dearg_types.
Context (Σ : global_env).

Fixpoint mkAppsBt (t : box_type) (us : list box_type) : box_type :=
  match us with
  | [] => t
  | a :: args => mkAppsBt (TApp t a) args
  end.

Fixpoint dearg_single_bt (tvars : list oib_type_var) (t : box_type) (args : list box_type)
  : box_type :=
  match tvars, args with
  | tvar :: tvars, arg :: args =>
    if tvar_is_logical tvar || negb (tvar_is_sort tvar) then
      dearg_single_bt tvars t args
    else
      dearg_single_bt tvars (TApp t arg) args
  | _, _ => mkAppsBt t args
  end.

Definition get_inductive_tvars (ind : inductive) : list oib_type_var :=
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
  | _ => bt
  end.

Definition debox_box_type (bt : box_type) : box_type :=
  debox_box_type_aux [] bt.

Definition debox_type_constant (cst : constant_body) : constant_body :=
  {| cst_type := on_snd debox_box_type (cst_type cst);
     cst_body := cst_body cst; |}.

Definition debox_type_oib (oib : one_inductive_body) : one_inductive_body :=
  {| ind_name := ind_name oib;
     ind_type_vars := filter (fun tvar => tvar_is_sort tvar && negb (tvar_is_logical tvar))
                             (ind_type_vars oib);
     ind_ctor_type_vars := ind_ctor_type_vars oib;
     ind_ctors := map (on_snd (map debox_box_type)) (ind_ctors oib);
     ind_projs := map (on_snd debox_box_type) (ind_projs oib); |}.

Definition debox_type_mib (mib : mutual_inductive_body) : mutual_inductive_body :=
  {| ind_npars := ind_npars mib; ind_bodies := map debox_type_oib (ind_bodies mib) |}.

Definition debox_type_decl (decl : global_decl) : global_decl :=
  match decl with
  | ConstantDecl cst => ConstantDecl (debox_type_constant cst)
  | InductiveDecl b mib => InductiveDecl b (debox_type_mib mib)
  | TypeAliasDecl _ => decl
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
  match cst_body cst with
  | Some body =>
    let max_lams := #|(decompose_TArr (cst_type cst).2).1| in
    let '(mask, (_, inds)) := analyze_top_level analyze ([], inds) max_lams body in
    (mask, inds)
  | None => (map is_box_or_any (decompose_TArr (cst_type cst).2).1, inds)
  end.

Record dearg_set := {
  const_masks : list (kername * bitmask);
  ind_masks : list (kername * mib_masks); }.

Fixpoint analyze_env (Σ : global_env) : dearg_set :=
  match Σ with
  | [] => {| const_masks := []; ind_masks := [] |}
  | (kn, decl) :: Σ =>
    let (consts, inds) := analyze_env Σ in
    let (consts, inds) :=
        match decl with
        | ConstantDecl cst =>
          let '(mask, inds) := analyze_constant cst inds in
          ((kn, mask) :: consts, inds)
        | InductiveDecl _ mib =>
          let ctor_masks :=
              List.concat
                (mapi (fun ind oib =>
                         mapi (fun c '(_, args) =>
                                 (ind, c, map is_box_or_any (skipn (ind_npars mib) args)))
                              (ind_ctors oib))
                      (ind_bodies mib)) in
          let mm := {| param_mask := List.repeat true (ind_npars mib);
                       ctor_masks := ctor_masks |} in
          (consts, (kn, mm) :: inds)
        | TypeAliasDecl _ => (consts, inds)
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
  let ds := analyze_env Σ in
  let ds := trim_dearg_set ds in
  let Σ := dearg_env (ind_masks ds) (const_masks ds) Σ in
  debox_env_types Σ.

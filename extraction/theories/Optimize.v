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

Local Open Scope string_scope.
Import ListNotations.
Import MonadNotation.
Set Equations Transparent.

Import EAstUtils.
Import Erasure.
Import ExAst.

Definition inspect {A} (x : A) : { a | a = x } :=
  exist x eq_refl.

(* Eta expand all constructors so they are applied to all their parameters *)
Section eta.
(* Ctors to eta expand *)
Context (ctors : list (inductive * nat * nat)).
(* Constants to eta expand *)
Context (constants : list (kername * nat)).

Definition eta_single (t : term) (args : list term) (count : nat) : term :=
  let needed := count - List.length args in
  let prev_args := map (lift0 needed) args in
  let eta_args := rev_map tRel (seq 0 needed) in
  nat_rect
    _
    (mkApps t (prev_args ++ eta_args))
    (fun _ => tLambda nAnon)
    needed.

Definition eta_ctor (ind : inductive) (c : nat) (args : list term) : term :=
  match find (fun '(ind', c', n) => eq_inductive ind' ind && (c' =? c)) ctors with
  | Some (_, _, n) => eta_single (tConstruct ind c) args n
  | None => mkApps (tConstruct ind c) args
  end.

Definition eta_const (kn : kername) (args : list term) : term :=
  match find (fun '(kn', n) => eq_kername kn' kn) constants with
  | Some (_, n) => eta_single (tConst kn) args n
  | None => mkApps (tConst kn) args
  end.

(*
Fixpoint decompose_lam_upto_n (n : nat) (t : term) : list name * term :=
  match n, t with
  | S n, tLambda na t => let (nas, t) := decompose_lam_upto_n n t in
                         (na :: nas, t)
  | _, _ => ([], t)
  end.

(* Unfortunate MetaCoq's typing does not impose any conditions on the shape of
   case branches, so we also have to eta expand those... *)
Definition eta_cases (ind : inductive) (brs : list (nat * term)) : list (nat * term) :=
  brs. (* todo *)
*)

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

Fixpoint eta_expand_aux (args : list term) (t : term) : term :=
  match t with
  | tApp hd arg => eta_expand_aux (eta_expand_aux [] arg :: args) hd
  | tConstruct ind c => eta_ctor ind c args
  | tConst kn => eta_const kn args
  (*| tCase (ind, npars) disc brs =>
    mkApps
      (tCase
         (ind, npars)
         (eta_expand_aux [] disc)
         (eta_cases ind (map (on_snd (eta_expand_aux [])) brs)))
      args*)
  | t => mkApps (map_subterms (eta_expand_aux []) t) args
  end.

Definition eta_expand (t : term) : term :=
  eta_expand_aux [] t.

Definition eta_expand_decl (decl : global_decl) : global_decl :=
  match decl with
  | ConstantDecl cst =>
    ConstantDecl
      {| cst_type := cst_type cst;
         cst_body := option_map eta_expand (cst_body cst) |}
  | _ => decl
  end.

Definition eta_expand_env (Σ : global_env) : global_env :=
  map (on_snd eta_expand_decl) Σ.

Lemma wfe_term_eta_single Σ t args n :
  wfe_term Σ t ->
  Forall (wfe_term Σ) args ->
  wfe_term Σ (eta_single t args n).
Proof.
  intros wft wfall.
  unfold eta_single.
  induction (_ - _) at 3; [|easy].
  cbn in *.
  apply wfe_term_mkApps; [easy|].
  apply Forall_app_inv.
  - clear -wfall.
    generalize args at 1; intros.
    induction wfall; cbn in *; [easy|].
    constructor; [|easy].
    now apply wfe_term_lift.
  - clear.
    induction (seq _ _); [cbn; easy|].
    rewrite rev_map_cons.
    apply Forall_app_inv; [easy|].
    constructor; easy.
Qed.

Lemma wfe_term_eta_ctor Σ ind i args :
  wfe_term Σ (tConstruct ind i) ->
  Forall (wfe_term Σ) args ->
  wfe_term Σ (eta_ctor ind i args).
Proof.
  intros wft wfall.
  unfold eta_ctor.
  destruct (find _ _) as [((? & ?) & ?)|].
  - now apply wfe_term_eta_single.
  - now apply wfe_term_mkApps.
Qed.

Lemma wfe_term_eta_const Σ kn args :
  wfe_term Σ (tConst kn) ->
  Forall (wfe_term Σ) args ->
  wfe_term Σ (eta_const kn args).
Proof.
  intros wft wfall.
  unfold eta_const.
  destruct (find _ _) as [((? & ?) & ?)|].
  - now apply wfe_term_eta_single.
  - now apply wfe_term_mkApps.
Qed.

Lemma wfe_term_eta_expand_aux Σ args t :
  Forall (wfe_term Σ) args ->
  wfe_term Σ t ->
  wfe_term Σ (eta_expand_aux args t).
Proof.
  revert args.
  induction t using term_forall_list_ind; intros args wfall wft; cbn in *; auto.
  - now apply wfe_term_mkApps.
  - now apply wfe_term_mkApps.
  - now apply wfe_term_mkApps.
  - apply wfe_term_mkApps; [|easy].
    now induction H; cbn in *.
  - now apply wfe_term_mkApps.
  - apply wfe_term_mkApps; cbn; easy.
  - apply IHt1; [|easy].
    constructor; [|easy].
    now apply IHt2.
  - now apply wfe_term_eta_const.
  - now apply wfe_term_eta_ctor.
  - apply wfe_term_mkApps; [|easy].
    cbn.
    destruct p.
    split; [easy|].
    split; [easy|].
    destruct wft as (_ & (_ & allwf)).
    induction X; cbn in *; easy.
  - now apply wfe_term_mkApps.
  - apply wfe_term_mkApps; [|easy].
    induction H; cbn in *; easy.
  - apply wfe_term_mkApps; [|easy].
    induction H; cbn in *; easy.
Qed.

Lemma wfe_term_eta_expand Σ t :
  wfe_term Σ t ->
  wfe_term Σ (eta_expand t).
Proof. now apply wfe_term_eta_expand_aux. Qed.

Lemma decompose_app_rec_app t acc acc' :
  let (hd, args) := decompose_app_rec t acc in
  decompose_app_rec t (acc ++ acc') = (hd, args ++ acc').
Proof.
  revert acc.
  induction t using term_forall_list_ind; intros acc; try easy.
  cbn.
  specialize (IHt1 (t2 :: acc)).
  now rewrite <- app_comm_cons in IHt1.
Qed.

Lemma eta_expand_aux_unfold t args :
  eta_expand_aux args t =
  match decompose_app t with
  | (tConstruct ind c, args') => eta_ctor ind c (map (eta_expand_aux []) args' ++ args)
  | (tConst kn, args') => eta_const kn (map (eta_expand_aux []) args' ++ args)
  | (hd, args') => mkApps
                     (map_subterms (eta_expand_aux []) hd)
                     (map (eta_expand_aux []) args' ++ args)
  end.
Proof.
  revert args.
  induction t using term_forall_list_ind; intros args; cbn in *;
    try easy.
  rewrite IHt1.
  unfold decompose_app.
  pose proof (decompose_app_rec_app t1 [] [t2]).
  destruct (decompose_app_rec t1 []) as [hd args'].
  cbn in *.
  rewrite H.
  rewrite map_app.
  cbn.
  now rewrite <- app_assoc.
Qed.

Lemma eta_expand_unfold t :
  eta_expand t =
  match decompose_app t with
  | (tConstruct ind c, args) => eta_ctor ind c (map eta_expand args)
  | (tConst kn, args) => eta_const kn (map eta_expand args)
  | (hd, args) => mkApps (map_subterms eta_expand hd) (map eta_expand args)
  end.
Proof.
  unfold eta_expand at 1.
  rewrite eta_expand_aux_unfold.
  destruct (decompose_app _).
  now rewrite app_nil_r.
Qed.


End eta.

Local Open Scope positive.
Definition set_bit (n : nat) (p : positive) : positive :=
  Pos.lor p (Pos.shiftl_nat 1 n).

Definition has_bit (n : nat) (p : positive) : bool :=
  Pos.testbit_nat p n.

Definition chop (p : positive) : positive :=
  match p with
  | p~0 => p
  | p~1 => p
  | XH => 1
  end.

Fixpoint bitmask_zeros (n : nat) : positive :=
  match n with
  | 0%nat => xH
  | S n => (bitmask_zeros n)~0
  end.

Fixpoint bitmask_ones (n : nat) : positive :=
  match n with
  | 0%nat => xH
  | S n => (bitmask_ones n)~1
  end.

Fixpoint lnot (p : positive) : positive :=
  match p with
  | p~0 => (lnot p)~1
  | p~1 => (lnot p)~0
  | xH => xH
  end.

(* Returns successor of the index of the last 1 in the bitmask *)
Definition S_last_1 (p : positive) : nat :=
  (fix f p i n :=
     match p with
     | xH => n
     | p~0 => f p (S i) n
     | p~1 => f p (S i) (S i)
     end) p 0%nat 0%nat.

Local Open Scope nat.
Fixpoint skip_mask (n : nat) (p : positive) : positive :=
  match n with
  | 0 => p
  | S n => skip_mask n (chop p)
  end.

Section dearg.
(* We are given bitmasks representing which args to remove *)
Context (ctors : list (inductive * nat * positive)).
Context (constants : list (kername * positive)).

Fixpoint unlift (n k : nat) (t : term) : term :=
  match t with
  | tRel i => if k <=? i then tRel (i - n) else tRel i
  | tEvar ev args => tEvar ev (map (unlift n k) args)
  | tLambda na M => tLambda na (unlift n (S k) M)
  | tLetIn na b b' => tLetIn na (unlift n k b) (unlift n (S k) b')
  | tApp u v => tApp (unlift n k u) (unlift n k v)
  | tCase ind c brs => let brs' := map (on_snd (unlift n k)) brs in tCase ind (unlift n k c) brs'
  | tProj p c => tProj p (unlift n k c)
  | tFix mfix idx =>
    let k' := #|mfix| + k in
    let mfix' := map (map_def (unlift n k')) mfix in
    tFix mfix' idx
  | tCoFix mfix idx =>
    let k' := #|mfix| + k in
    let mfix' := map (map_def (unlift n k')) mfix
    in tCoFix mfix' idx
  | _ => t
  end.

Fixpoint dearg_single (mask : positive) (t : term) (args : list term) : term :=
  match mask, args with
  | mask~1, arg :: args => dearg_single mask t args
  | mask~0, arg :: args => dearg_single mask (tApp t arg) args
  | _, _ => mkApps t args
            (* todo: pass through conditions saying that we never run out of args, only mask? *)
  end.

Definition dearg_ctor (ind : inductive) (c : nat) (args : list term) : term :=
  match find (fun '(ind', c', _) => eq_inductive ind' ind && (c' =? c)) ctors with
  | Some (_, _, mask) => dearg_single mask (tConstruct ind c) args
  | None => mkApps (tConstruct ind c) args
  end.

Definition dearg_const (kn : kername) (args : list term) : term :=
  match find (fun '(kn', _) => eq_kername kn' kn) constants with
  | Some (_, mask) => dearg_single mask (tConst kn) args
  | None => mkApps (tConst kn) args
  end.

Fixpoint dearg_lambdas (mask : positive) (ar : nat) (t : term) : nat * term :=
  match mask, t with
  | mask~1, tLambda na body => dearg_lambdas mask (ar - 1) (unlift 1 0 body)
  | mask~0, tLambda na body => let (ar, t) := dearg_lambdas mask ar body in
                               (ar, tLambda na t)
  | _, _ => (ar, t)
  end.

Definition dearg_case_branches
           (ind : inductive)
           (npars : nat)
           (brs : list (nat * term)) : list (nat * term) :=
  let dearg_one c br :=
      match find (fun '(ind', c', _) => eq_inductive ind' ind && (c' =? c)) ctors with
      | Some (_, _, mask) => dearg_lambdas (skip_mask npars mask) br.1 br.2
      | None => br
      end in
  mapi dearg_one brs.

Fixpoint dearg_aux (args : list term) (t : term) : term :=
  match t with
  | tApp hd arg => dearg_aux (dearg_aux [] arg :: args) hd
  | tConstruct ind c => dearg_ctor ind c args
  | tConst kn => dearg_const kn args
  | tCase (ind, npars) discr brs =>
    (* todo: what to do about parameters? Right now we remove them
       in a separate pass. *)
    mkApps
      (tCase
         (ind, npars)
         (dearg_aux [] discr)
         (dearg_case_branches ind npars (map (on_snd (dearg_aux [])) brs)))
      args
  | t => mkApps (map_subterms (dearg_aux []) t) args
  end.

(* Remove lambda abstractions from top level declaration based on bitmask *)
Fixpoint dearg_cst_top
         (mask : positive)
         (type : box_type)
         (body : term) : box_type * term :=
  match mask, type, body with
  | _, _, tLetIn na val body =>
    let (type, body) := dearg_cst_top mask type body in
    (type, tLetIn na val body)
  | mask~1, TArr _ cod, tLambda _ body =>
    let (type, body) := dearg_cst_top mask cod body in
    (type, unlift 1 0 body)
  | mask~0, TArr dom cod, tLambda na body =>
    let (cod, body) := dearg_cst_top mask cod body in
    (TArr dom cod, tLambda na body)
  | _, _, _ => (type, body)
  end.

(* Remove lambda abstractions from top level declaration and remove
   all unused args in applicacations *)
Definition dearg_cst (kn : kername) (cst : constant_body) : constant_body :=
  let cst :=
      match find (fun '(kn', _) => eq_kername kn' kn) constants with
      | Some (_, _, mask) =>
        match cst_body cst with
        | Some body =>
          let (new_type, new_body) := dearg_cst_top mask (cst_type cst).2 body in
          {| cst_type := ((cst_type cst).1, new_type); cst_body := Some new_body |}
        | None => cst
        end
      | None => cst
      end in
  {| cst_type := cst_type cst; cst_body := option_map (dearg_aux []) (cst_body cst) |}.

(* Remove all data from ctor based on bitmask *)
Fixpoint dearg_oib_ctor (mask : positive) (bts : list box_type) : list box_type :=
  match mask, bts with
  | mask~0, bt :: bts => bt :: dearg_oib_ctor mask bts
  | mask~1, bt :: bts => dearg_oib_ctor mask bts
  | _, _ => bts
  end.

Definition dearg_oib (ind : inductive) (oib : one_inductive_body) : one_inductive_body :=
  {| ind_name := ind_name oib;
     ind_type_vars := ind_type_vars oib;
     ind_ctors :=
       mapi (fun c '(name, bts) =>
               match find (fun '(ind', c', _) => eq_inductive ind' ind && (c' =? c)) ctors with
               | Some (_, _, mask) => (name, dearg_oib_ctor mask bts)
               | None => (name, bts)
               end)
            (ind_ctors oib);
     ind_projs := ind_projs oib |}.

Definition dearg_mib (kn : kername) (mib : mutual_inductive_body) : mutual_inductive_body :=
  {| ind_npars := ind_npars mib;
     ind_bodies := mapi (fun i => dearg_oib {| inductive_mind := kn;
                                               inductive_ind := i |})
                        (ind_bodies mib) |}.

Definition dearg_decl (kn : kername) (decl : global_decl) : global_decl :=
  match decl with
  | ConstantDecl cst => ConstantDecl (dearg_cst kn cst)
  | InductiveDecl mib => InductiveDecl (dearg_mib kn mib)
  end.

Definition dearg_env (Σ : global_env) : global_env :=
  map (fun '(kn, decl) => (kn, dearg_decl kn decl)) Σ.

End dearg.

Local Open Scope nat.
Fixpoint delete_parameters_term (t : term) : term :=
  match t with
  | tCase (ind, npars) discr brs =>
    tCase (ind, 0) (delete_parameters_term discr) (map (on_snd delete_parameters_term) brs)
  | t => map_subterms delete_parameters_term t
  end.

Definition delete_parameters_decl (decl : global_decl) : global_decl :=
  match decl with
  | ConstantDecl cst =>
    ConstantDecl
      {| cst_type := cst_type cst;
         cst_body := option_map delete_parameters_term (cst_body cst); |}
  | InductiveDecl mib =>
    InductiveDecl
      {| ind_npars := 0;
         ind_bodies := ind_bodies mib |}
  end.

Definition make_parameter_dearg_masks (Σ : global_env) : list (inductive * nat * positive) :=
  flat_map
    (fun '(kn, decl) =>
       match decl with
       | InductiveDecl mib =>
         let mask := bitmask_ones (ind_npars mib) in
         let oib_ctors i oib :=
             let ind := {| inductive_mind := kn; inductive_ind := i |} in
             mapi (fun c _ => (ind, c, mask)) (ind_ctors oib) in
         List.concat (mapi oib_ctors (ind_bodies mib))
       | _ => []
       end)
    Σ.

(* Remove parameters from all inductives *)
Definition remove_parameters (Σ : global_env) : global_env :=
  let ctors := make_parameter_dearg_masks Σ in
  let ctors_eta_count := map (fun '(ind, c, mask) => (ind, c, S_last_1 mask)) ctors in
  let Σ := eta_expand_env ctors_eta_count [] Σ in
  let Σ := dearg_env ctors [] Σ in
  map (on_snd delete_parameters_decl) Σ.

(* Return bitmask indicating which context variables have uses *)
Fixpoint used_context_vars (Γ : positive) (t : term) : positive :=
  match t with
  | tBox => Γ
  | tRel i => set_bit i Γ
  | tVar n => Γ
  | tEvar _ ts => fold_right Pos.lor Γ (map (used_context_vars Γ) ts)
  | tLambda _ cod => chop (used_context_vars Γ~0 cod)
  | tLetIn _ val body => chop (used_context_vars (used_context_vars Γ val)~0 body)
  | tApp hd arg => used_context_vars (used_context_vars Γ hd) arg
  | tConst _ => Γ
  | tConstruct _ _ => Γ
  | tCase _ disc brs =>
    let Γ := used_context_vars Γ disc in
    fold_right Pos.lor Γ (map (used_context_vars Γ ∘ snd) brs)
  | tProj _ t => used_context_vars Γ t
  | tFix def _
  | tCoFix def _ => fold_right Pos.lor Γ (map (used_context_vars Γ ∘ dbody) def)
  end.

(* Return bitmask indicating which parameters are used by the
specified lambda abstractions. All parameters after the end of
the bit mask should be assumed to be used. *)
Fixpoint func_body_used_params (Γ : positive) (t : term) (ty : box_type) : positive :=
  match t, ty with
  | tLetIn na val body, ty =>
    let Γ := used_context_vars Γ val in
    chop (func_body_used_params Γ~0 body ty)
  | tLambda na body, TArr hd ty =>
    func_body_used_params Γ~0 body ty
  | t, ty => used_context_vars Γ t
  end.

Fixpoint bitmask_rev_aux (p : positive) (acc : positive) : positive :=
  match p with
  | xH => acc
  | p~0 => bitmask_rev_aux p (acc~0)
  | p~1 => bitmask_rev_aux p (acc~1)
  end.

Definition bitmask_rev (p : positive) : positive :=
  bitmask_rev_aux p xH.

Definition constant_used_params (cst : constant_body) : positive :=
  match cst_body cst with
  | None => xH
  | Some body => bitmask_rev (func_body_used_params xH body (cst_type cst).2)
  end.

Fixpoint mask_from_ctor_types (bts : list box_type) : positive :=
  match bts with
  | [] => xH
  | TBox :: bts
  | TAny :: bts => (mask_from_ctor_types bts)~0
  | _ :: bts => (mask_from_ctor_types bts)~1
  end.

Definition ind_ctors_used_params
           (kn : kername)
           (ind : mutual_inductive_body) : list (inductive * nat * positive) :=
  List.concat
    (mapi
       (fun i oib =>
          let ind := {| inductive_mind := kn; inductive_ind := i |} in
          mapi (fun c '(name, bts) => (ind, c, mask_from_ctor_types bts))
               (ind_ctors oib))
       (ind_bodies ind)).

Record used_set := {
  used_function_params : list (kername * positive);
  used_ctor_params : list (inductive * nat * positive); }.

Fixpoint find_used_set (Σ : global_env) : used_set :=
  match Σ with
  | [] => {| used_ctor_params := []; used_function_params := [] |}
  | (kn, decl) :: Σ =>
    let (funcs, ctors) := find_used_set Σ in
    let (funcs, ctors) :=
        match decl with
        | ConstantDecl cst => ((kn, constant_used_params cst) :: funcs, ctors)
        | InductiveDecl ind => (funcs, ind_ctors_used_params kn ind ++ ctors)
        end in
    {| used_function_params := funcs; used_ctor_params := ctors |}
  end.

Definition remove_unused_args (Σ : global_env) : global_env :=
  let used_set := find_used_set Σ in
  let dearg_const_masks := map (on_snd lnot) (used_function_params used_set) in
  let dearg_ctor_masks := map (fun '(ind, c, use_mask) => (ind, c, lnot use_mask))
                              (used_ctor_params used_set) in
  let consts_eta_count := map (on_snd S_last_1) dearg_const_masks in
  let ctors_eta_count := map (fun '(ind, c, mask) => (ind, c, S_last_1 mask)) dearg_ctor_masks in
  let Σ := eta_expand_env ctors_eta_count consts_eta_count Σ in
  dearg_env dearg_ctor_masks dearg_const_masks Σ.

(*
Local Open Scope nat.
Fixpoint uses_var (db : nat) (t : term) : bool :=
  match t with
  | tBox => false
  | tRel i => i =? db
  | tVar _ => false
  | tEvar _ ts => fold_right orb false (map (uses_var db) ts)
  | tLambda _ cod => uses_var (S db) cod
  | tLetIn _ val body => uses_var db val || uses_var (S db) body
  | tApp hd arg => uses_var db hd || uses_var db arg
  | tConst _ => false
  | tConstruct _ _ => false
  | tCase _ disc brs =>
    fold_right orb (uses_var db disc) (map (uses_var db ∘ snd) brs)
  | tProj _ t => uses_var db t
  | tFix def _
  | tCoFix def _ => fold_right orb false (map (uses_var db ∘ dbody) def)
  end.

Definition uses_var_decision (n : nat) (t : term) : Type :=
  {uses_var n t} + {~uses_var n t}.

Fixpoint use_annots (t : term) : Type :=
  match t with
  | tBox => unit
  | tRel _ => unit
  | tVar _ => unit
  | tEvar _ ts => fold_right prod unit (map use_annots ts)
  | tLambda _ cod => uses_var_decision 0 cod × use_annots cod
  | tLetIn _ val body => use_annots val * uses_var_decision 0 body * use_annots body
  | tApp hd arg => use_annots hd × use_annots arg
  | tConst _ => unit
  | tConstruct _ _ => unit
  | tCase _ disc brs =>
    use_annots disc × fold_right prod unit (map (use_annots ∘ snd) brs)
  | tProj _ t => use_annots t
  | tFix def _
  | tCoFix def _ => fold_right prod unit (map (use_annots ∘ dbody) def)
  end.

(* TODO: This can be optimized. A lot. *)
Equations annotate (t : term) : use_annots t :=
annotate tBox := tt;
annotate (tRel _) := tt;
annotate (tVar _) := tt;
annotate (tEvar _ ts) := annot_ts ts
where annot_ts (ts : list term) : fold_right prod unit (map use_annots ts) := {
annot_ts [] := tt;
annot_ts (t :: ts) := (annotate t, annot_ts ts)
};
annotate (tLambda _ cod) with inspect (uses_var 0 cod) := {
  | exist true _ := (left _, annotate cod);
  | exist false _ := (right _, annotate cod)
  };
annotate (tLetIn _ val body) with inspect (uses_var 0 body) := {
  | exist true _ := (annotate val, left _, annotate body);
  | exist false _ := (annotate val, right _, annotate body)
  };
annotate (tApp hd arg) := (annotate hd, annotate arg);
annotate (tConst _) := tt;
annotate (tConstruct _ _) := tt;
annotate (tCase _ disc brs) := (annotate disc, annot_brs brs)
where annot_brs (brs : list (nat × term)) : fold_right prod unit (map (use_annots ∘ snd) brs) := {
annot_brs [] := tt;
annot_brs ((_, t) :: brs) := (annotate t, annot_brs brs)
};
annotate (tProj _ t) := annotate t;
annotate (tFix defs _) := annot_defs defs
where annot_defs (defs : list (def term)) : fold_right prod unit (map (use_annots ∘ dbody) defs) := {
annot_defs [] := tt;
annot_defs (d :: defs) := (annotate (dbody d), annot_defs defs)
};
annotate (tCoFix defs _) := annot_defs defs
where annot_defs (defs : list (def term)) : fold_right prod unit (map (use_annots ∘ dbody) defs) := {
annot_defs [] := tt;
annot_defs (d :: defs) := (annotate (dbody d), annot_defs defs)
}.
Next Obligation. congruence. Qed.
Next Obligation. congruence. Qed.

Definition decl_marks (decl : global_decl) : Type :=
  match decl with
  | ConstantDecl cst => list bool
  | InductiveDecl mib =>
    (* constructors are simple enough that we just look them up directly *)
    unit
  end.

Definition global_env_marks (Σ : global_env) : Type :=
  fold_right prod unit (map (decl_marks ∘ snd) Σ).

Equations lookup_const_marks
          (Σ : global_env)
          (marks : global_env_marks Σ)
          (kn : kername) : list bool :=
lookup_const_marks [] _ _ := [];
lookup_const_marks ((dkn, ConstantDecl cst) :: Σ) (marks, rest) kn with eq_kername dkn kn := {
  | true := marks;
  | false := lookup_const_marks Σ rest kn
  };
lookup_const_marks (_ :: Σ) (_, rest) kn := lookup_const_marks Σ rest kn.

Fixpoint mark_parameters (bt : box_type) (tm : term) : list bool :=
  match bt, tm with
  | TArr dom cod, tLambda _ res =>
    match dom with
    | TBox => true
    | _ => false
    end :: mark_parameters cod res
  | _, _ => []
  end.

Equations mark_constants (Σ : global_env) : global_env_marks Σ :=
mark_constants [] := tt;
mark_constants ((kn, decl) :: Σ) := (mark_decl decl, mark_constants Σ)
  where mark_decl (decl : global_decl) : decl_marks decl :=
  mark_decl (ConstantDecl cst) with cst_body cst := {
    | Some body := mark_parameters (cst_type cst).2 body;
    | None := []
    };
  mark_decl (InductiveDecl _) := tt.

*)

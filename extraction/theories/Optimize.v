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

End eta.

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

Fixpoint bitmask_not (bs : bitmask) : bitmask :=
  map negb bs.

Definition count_zeros (bs : bitmask) : nat :=
  List.length (filter negb bs).

(* Returns successor of the index of the last 1 in the bitmask *)
Definition S_last_1 (bs : bitmask) : nat :=
  (fix f bs i n :=
     match bs with
     | [] => n
     | false :: bs => f bs (S i) n
     | true :: bs => f bs (S i) (S i)
     end) bs 0%nat 0%nat.

Fixpoint bitmask_or (bs1 bs2 : bitmask) : bitmask :=
  match bs1, bs2 with
  | b1 :: bs1, b2 :: bs2 => (b1 || b2) :: bitmask_or bs1 bs2
  | [], bs2 => bs2
  | bs1, [] => bs1
  end.

Section dearg.
Record mib_masks := {
  param_mask : bitmask;
  ctor_masks : list (nat * nat * bitmask); }.

Context (ind_masks : list (kername * mib_masks)).
(* Bitmask for each constructor specifying which parameters to remove, **excluding parameters** *)
Context (const_masks : list (kername * bitmask)).

Definition get_mib_masks (kn : kername) : option mib_masks :=
  option_map snd (find (fun '(kn', _) => eq_kername kn' kn) ind_masks).

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

Fixpoint dearg_single (mask : bitmask) (t : term) (args : list term) : term :=
  match mask, args with
  | true :: mask, arg :: args => dearg_single mask t args
  | false :: mask, arg :: args => dearg_single mask (tApp t arg) args
  | _, _ => mkApps t args
            (* todo: pass through conditions saying that we never run out of args, only mask? *)
  end.

Definition dearg_ctor (ind : inductive) (c : nat) (args : list term) : term :=
  let mask :=
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
      end in
  dearg_single mask (tConstruct ind c) args.

Definition dearg_const (kn : kername) (args : list term) : term :=
  match find (fun '(kn', _) => eq_kername kn' kn) const_masks with
  | Some (_, mask) => dearg_single mask (tConst kn) args
  | None => mkApps (tConst kn) args
  end.

Fixpoint dearg_lambdas (mask : bitmask) (ar : nat) (t : term) : nat * term :=
  match mask, t with
  | true :: mask, tLambda na body => dearg_lambdas mask (ar - 1) (unlift 1 0 body)
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
  | tConstruct ind c => dearg_ctor ind c args
  | tConst kn => dearg_const kn args
  | tCase (ind, npars) discr brs =>
    let discr := dearg_aux [] discr in
    let brs := map (on_snd (dearg_aux [])) brs in
    mkApps (dearg_case ind npars discr brs) args
  | t => mkApps (map_subterms (dearg_aux []) t) args
  end.

(* Remove lambda abstractions from top level declaration based on bitmask *)
Fixpoint dearg_cst_top
         (mask : bitmask)
         (type : box_type)
         (body : term) : box_type * term :=
  match mask, type, body with
  | _, _, tLetIn na val body =>
    let (type, body) := dearg_cst_top mask type body in
    (type, tLetIn na val body)
  | true :: mask, TArr _ cod, tLambda _ body =>
    let (type, body) := dearg_cst_top mask cod body in
    (type, unlift 1 0 body)
  | false :: mask, TArr dom cod, tLambda na body =>
    let (cod, body) := dearg_cst_top mask cod body in
    (TArr dom cod, tLambda na body)
  | _, _, _ => (type, body)
  end.

(* Remove lambda abstractions from top level declaration and remove
   all unused args in applicacations *)
Definition dearg_cst (kn : kername) (cst : constant_body) : constant_body :=
  let cst :=
      match find (fun '(kn', _) => eq_kername kn' kn) const_masks with
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
    let Γfix := fold_right bitmask_or Γ (map (used_context_vars Γfix ∘ dbody) defs) in
    skipn #|defs| Γfix
  end.

(* Return bitmask indicating which parameters are used by the
specified lambda abstractions. All parameters after the end of
the bit mask should be assumed to be used. *)
Fixpoint func_body_used_params (Γ : bitmask) (t : term) (ty : box_type) : bitmask :=
  match t, ty with
  | tLetIn na val body, ty =>
    let Γ := used_context_vars Γ val in
    tl (func_body_used_params (false :: Γ) body ty)
  | tLambda na body, TArr hd ty =>
    func_body_used_params (false :: Γ) body ty
  | t, ty => used_context_vars Γ t
  end.

Definition constant_used_params (cst : constant_body) : bitmask :=
  match cst_body cst with
  | None => []
  | Some body => List.rev (func_body_used_params [] body (cst_type cst).2)
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

Definition remove_unused_args (Σ : global_env) : global_env :=
  let dearg_set := get_dearg_set_for_unused_args Σ in
  let consts_eta_count := map (on_snd S_last_1) (const_masks dearg_set) in
  let get_ctors_eta_count kn mib_masks :=
      map (fun '(i, c, mask) => ({| inductive_mind := kn; inductive_ind := i |}, c,
                                 List.length (param_mask mib_masks) + S_last_1 mask))
          (ctor_masks mib_masks) in
  let ctors_eta_count :=
      List.concat
        (map (fun '(kn, mib_masks) => get_ctors_eta_count kn mib_masks)
             (ind_masks dearg_set)) in
  let Σ := eta_expand_env ctors_eta_count consts_eta_count Σ in
  dearg_env (ind_masks dearg_set) (const_masks dearg_set) Σ.

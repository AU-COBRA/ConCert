(** * Eta-expansion and proof generation **)

(** We perform eta-expansion of template-coq terms and generate proofs that
    we terms are equal to the originals. Since eta-conversion is part of the
    Coq's conversion, the proof is essentially [eq_refl].
    All dependencies are also expanded.*)

From Coq Require Import List PeanoNat Bool String.
From MetaCoq.Template Require Import Kernames All.
From ConCert.Extraction Require Import Erasure Optimize Common ResultMonad Extraction.
Open Scope string.
Open Scope nat.

Import Template.Ast.
Import ListNotations.
Import MonadNotation.

Section Eta.
  Definition ctors_info := list (inductive
                                 * nat (* constructor number *)
                                 * nat (* how much to expand *)
                                 * term (* constructor's type *)
                                ).
  Definition constansts_info := list (kername * nat * term).

  Context (ctors : ctors_info).
  Context (constants : constansts_info).
  Context (Σ : global_env).

  Fixpoint remove_top_prod (t : Ast.term) (n : nat) :=
    match n,t with
    | O, _  => t
    | S m, tProd nm ty1 ty2 => remove_top_prod ty2 m
    | _, _ => t
    end.

  (** Eta-expands the given term of the form [(t args)].

      [Γ] -- context used to specialise the type of the term along with the arguments [args];
             particularly useful for eta-expanding constructors -- contains the list of inductives the constructor belongs to;
      [t] -- a term;
      [args] -- arguments to which the term is applied;
      [ty] -- the term's type;
      [count] -- how much to expand *)
  Definition eta_single (Γ : list term) (t : Ast.term) (args : list Ast.term) (ty : Ast.term) (count : nat): term :=
    let needed := count - #|args| in
    let prev_args := map (lift0 needed) args in
    let eta_args := rev_map tRel (seq 0 needed) in
    let cut_ty := remove_top_prod ty #|args| in
    (* NOTE: we substitute the arguments and the context Γ in order to "specialise" the term's type *)
    let subst_ty := subst (rev args ++ rev Γ ) 0 cut_ty in
    let remaining := firstn needed (decompose_prod subst_ty).1.2 in
    let remaining_names := firstn needed (decompose_prod subst_ty).1.1 in
    fold_right (fun '(nm,ty) b => Ast.tLambda nm ty b) (mkApps t (prev_args ++ eta_args)) (combine remaining_names remaining).


  Record ind_info :=
    { ind_info_inductive : inductive;
      ind_info_nmind : nat (* how many mutual inductives in the definition *)
    }.

  Definition eta_ctor (ind_i : ind_info) (c : nat)
           (u : Instance.t)
           (args : list term) : term :=
    let ind := ind_i.(ind_info_inductive) in
    match find (fun '(ind', c', _, _) => eq_inductive ind' ind && (c' =? c)) ctors with
    | Some (_, _,n,ty) =>
      let ind := mkInd ind.(inductive_mind) ind.(inductive_ind) in
      let Γind := map
                    (fun i => tInd (mkInd ind.(inductive_mind) i) [])
                    (seq 0 (ind_i.(ind_info_nmind))) in
      eta_single Γind (Ast.tConstruct ind c u) args ty n
    | None => mkApps (tConstruct ind c u) args
    end.

Definition eta_const (kn : kername) (u : Instance.t) (args : list term) : term :=
  match find (fun '(kn',n, _) => eq_kername kn' kn) constants with
  | Some (_, n, ty) => eta_single [] (tConst kn u) args ty n
  | None => mkApps (tConst kn u) args
  end.

Definition get_ind_info (ind : inductive) : option ind_info :=
   match lookup_env Σ ind.(inductive_mind) with
      | Some (InductiveDecl mib) =>
        let n_mind := mib.(ind_bodies) in
        Some {| ind_info_inductive := ind; ind_info_nmind := #|n_mind| |}
      | _ => None
   end.

(** We assume that all applications are "flattened" e.g. of the form
    [tApp hd [t1; t2; t3; ...; tn]] where hd itself is not an application.
    This is guaranteed for quoted terms. *)
Fixpoint eta_expand (t : term) : term :=
  match t with
  | tApp hd args =>
    match hd with
    | tConstruct ind c u =>
      match get_ind_info ind with
      | Some ind_i => eta_ctor ind_i c u (map eta_expand args)
      | _ => tVar ("Error: lookup of an inductive failed for "
                    ++ string_of_kername ind.(inductive_mind))
      end

    | tConst kn u => eta_const kn u (map eta_expand args)
    | _ => mkApps (eta_expand hd) (map eta_expand args)
    end
  | tEvar n ts => tEvar n (map eta_expand ts)
  | tLambda na ty body => tLambda na ty (eta_expand body)
  | tLetIn na val ty body => tLetIn na (eta_expand val) ty (eta_expand body)
  | tCase p ty disc brs =>
    tCase p ty (eta_expand disc) (map (on_snd eta_expand) brs)
  | tProj p t => tProj p (eta_expand t)
  | tFix def i => tFix (map (map_def id eta_expand) def) i
  | tCoFix def i => tCoFix (map (map_def id eta_expand) def) i
  (* NOTE: we know that constructros and constants are not applied at this point,
     since applications are captured by the previous cases *)
  | tConstruct ind c u =>
    match get_ind_info ind with
    | Some ind_i => eta_ctor ind_i c u (map eta_expand [])
    | None => tVar ("Error: lookup of an inductive failed for "
                     ++ string_of_kername ind.(inductive_mind))
    end
  | tConst kn u => eta_const kn u (map eta_expand [])
  | t => t
  end.

End Eta.

Definition from_oib (ds : dearg_set) (kn : kername) (ind_index : nat) (oib : one_inductive_body) : ctors_info :=
  let f i '(_, ty, c) :=
      let ind := mkInd kn ind_index in
      let mm := get_mib_masks ds.(ind_masks) kn in
      match mm with
      | Some m =>
        let cm := get_ctor_mask ds.(ind_masks) ind i in
        Some (ind,i,#|cm|,ty)
      | None => None
      end in
  fold_lefti (fun i acc c => match f i c with Some v => v :: acc| None => acc end)
             0  oib.(ind_ctors) [].

Fixpoint get_eta_info (Σ : global_env) (ds : dearg_set) : ctors_info * constansts_info :=
  match Σ with
  | (kn, InductiveDecl mib) :: Σ' =>
    let '(ctors, consts) := get_eta_info Σ' ds in
    (List.concat (mapi (from_oib ds kn) mib.(ind_bodies)) ++ ctors, consts)%list
  | (kn, ConstantDecl cb) :: Σ' =>
    let '(ctors, consts) := get_eta_info Σ' ds in
    (ctors, (kn, #|get_const_mask ds.(const_masks) kn|, cb.(cst_type)) :: consts)
  | [] => ([],[])
  end.

Fixpoint change_modpath (mpath : modpath) (ignore : kername -> bool) (t : term) : term :=
  match t with
  | tRel n => t
  | tVar id => t
  | tSort s => t
  | tEvar ev args => tEvar ev (map (change_modpath mpath ignore) args)
  | tCast t kind v => tCast (change_modpath mpath ignore t) kind (change_modpath mpath ignore v)
  | tProd na ty body => tProd na (change_modpath mpath ignore ty) (change_modpath mpath ignore body)
  | tLambda na ty body => tLambda na (change_modpath mpath ignore ty) (change_modpath mpath ignore body)
  | tLetIn na def def_ty body =>
    tLetIn na (change_modpath mpath ignore def) (change_modpath mpath ignore def_ty) (change_modpath mpath ignore body)
  | tApp f args => tApp (change_modpath mpath ignore f) (map (change_modpath mpath ignore) args)
  | tConst kn u => if ignore kn then t
                  else tConst (mpath, kn.2 ++ "_expanded") u
  | tInd ind u => t
  | tConstruct ind idx u => t
  | tCase ind_and_nbparams type_info discr branches =>
    tCase ind_and_nbparams (change_modpath mpath ignore type_info)
          (change_modpath mpath ignore discr) (map (on_snd (change_modpath mpath ignore)) branches)
  | tProj proj t => tProj proj (change_modpath mpath ignore t)
  | tFix mfix idx => tFix (map (map_def (change_modpath mpath ignore) (change_modpath mpath ignore)) mfix) idx
  | tCoFix mfix idx => tCoFix (map (map_def (change_modpath mpath ignore) (change_modpath mpath ignore)) mfix) idx
  end.

Definition generate_proof (Σ1 Σ2 : global_env) (kn1 kn2 : kername) : TemplateMonad (term × term × term × term) :=
  match lookup_env Σ1 kn1, lookup_env Σ2 kn2  with
  | Some (ConstantDecl cb1), Some (ConstantDecl cb2) =>
    match cb1.(cst_body), cb2.(cst_body) with
    | Some _, Some exp_body =>
      let ty := cb1.(cst_type) in
      let proof_ty :=
          tApp (tInd
                  {| inductive_mind := (MPfile ["Logic"; "Init"; "Coq"], "eq");
                     inductive_ind := 0 |} [])
               [ty; tConst kn1 []; tConst kn2 []] in
      let proof_body := tApp (tConstruct
                          {| inductive_mind := (MPfile ["Logic"; "Init"; "Coq"], "eq");
                             inductive_ind := 0 |} 0 [])
                       [ty;tConst kn1 []] in
      ret (cb1.(cst_type), (exp_body, (proof_ty, proof_body)))
    | _,_ => tmFail "No body"
    end
  | None, _ => tmFail ("Not found: " ++ kn1.2)
  | _, None => tmFail ("Not found: " ++ kn2.2)
  | _,_ => tmFail "Not a constant"
  end.

Definition gen_proof_prog (Σ1 Σ2 : global_env) (kn1 kn2 : kername) : TemplateMonad unit :=
  '(exp_ty, (exp_t, (p_ty, p_t))) <- generate_proof Σ1 Σ2 kn1 kn2 ;;
  tmBind (tmUnquoteTyped Type exp_ty)
         (fun A => ucst <- tmUnquoteTyped A exp_t ;;
                 tmDefinition kn2.2 ucst;;
            tmBind (tmUnquoteTyped Type p_ty)
                   (fun B =>
                      uproof <- tmUnquoteTyped B p_t ;;
                      tmDefinition (kn2.2++"_correct") uproof ;;
                      tmPrint B)).

Definition contains_global_env (Σ : global_env) (kn : kername) :=
  match lookup_env Σ kn with
  | Some v => true
  | None => false
  end.

Definition restrict_env (Σ : global_env) (kns : list kername) : global_env :=
  filter (fun '(kn, _) => match find (eq_kername kn) kns with
                       | Some _ => true
                       | None => false
                       end) Σ.

Fixpoint map_constants_global_env (k : kername -> kername) (f : constant_body -> constant_body) (Σ : global_env) : global_env :=
  match Σ with
  | [] => []
  | (kn, ConstantDecl cb) :: Σ' => (k kn, ConstantDecl (f cb)) :: map_constants_global_env k f Σ'
  | gd :: Σ' => gd :: map_constants_global_env k f Σ'
  end.

Definition add_suffix_global_env (mpath : modpath) (ignore : kername -> bool) (Σ : global_env) :=
  map_constants_global_env
    (fun kn => (mpath,kn.2 ++ "_expanded"))
    (fun cb => {| cst_type := cb.(cst_type);
               cst_body := b <- cb.(cst_body);;
                           Some (change_modpath mpath ignore b);
                cst_universes := cb.(cst_universes) |}) Σ.

Definition eta_global_env
           (trim_consts trim_inds : bool)
           (Σ : global_env) (seeds : KernameSet.t) (ignore : kername -> bool) :=
  let Σe :=
      erase_global_decls_deps_recursive
        (TemplateToPCUIC.trans_global_decls Σ) (assume_env_wellformed _)
        seeds ignore in
  let (const_masks, ind_masks) := analyze_env Σe in
  let const_masks := (if trim_consts then trim_const_masks else id) const_masks in
  let ind_masks := (if trim_inds then trim_ind_masks else id) ind_masks in
  let f cb :=
      match cb.(cst_body) with
      | Some b => let (ctors, consts) := get_eta_info Σ {| ind_masks := ind_masks;
                                                           const_masks := const_masks |} in
                  {| cst_type := cb.(cst_type);
                     cst_body := Some (eta_expand ctors consts Σ b);
                     cst_universes := cb.(cst_universes) |}
      | None => cb
      end in
  let Σ' := restrict_env Σ (map (fun '(kn, _, _) => kn) Σe) in
  map_constants_global_env id f Σ'.

Definition is_none {A} (o : option A) :=
  match o with
  | Some _ => false
  | None => true
  end.

Definition gen_expanded_const_and_proof (Σ : global_env) (mpath : modpath) (ignore : kername -> bool)  : TemplateMonad unit :=
  let Σdecls := filter (fun '(kn,gd) => match gd with
                                    | ConstantDecl cb => negb (is_none cb.(cst_body))
                                    | _ => false
                                     end) Σ in
  Σdecls' <- tmEval lazy (add_suffix_global_env mpath ignore Σdecls) ;;
  monad_iter (fun kn1 => gen_proof_prog Σ Σdecls' kn1 (mpath,kn1.2 ++ "_expanded"))
             (List.rev (map fst Σdecls)).

Definition eta_global_env_template
           (trim_consts trim_inds : bool)
           (mpath : modpath)
           (Σ : global_env)
           (seeds : KernameSet.t) (ignore : kername -> bool)
           (cst_name_ignore : kername -> bool) : TemplateMonad global_env :=
  Σext <- tmEval lazy (eta_global_env trim_consts trim_inds Σ seeds ignore);;
  gen_expanded_const_and_proof Σext mpath cst_name_ignore;;
  ret Σext.

Definition eta_expand_def {A} (trim_inds trim_consts : bool) (mpath : modpath) (cst_name_ignore : kername -> bool) (def : A) : TemplateMonad _ :=
  p <- tmQuoteRecTransp def false ;;
  kn <- extract_def_name def ;;
  eta_global_env_template
    trim_inds trim_consts mpath p.1
    (KernameSet.singleton kn) (fun _ => false) cst_name_ignore.

Module Examples.

  Module Ex1.
  Definition partial_app_pair :=
    let p : forall B : Type, unit -> B -> unit × B:= @pair unit in
    p bool tt true.
  End Ex1.
  MetaCoq Quote Recursively Definition p_app_pair_syn := Ex1.partial_app_pair.

  Definition anchor := fun x : nat => x.
  Definition CURRENT_MODULE := Eval compute in <%% anchor %%>.1.

  Definition modpath_eq_dec (mp1 mp2 : modpath) : {mp1 = mp2} + {mp1 <> mp2}.
    repeat decide equality.
  Defined.

  Definition eq_modpath (mp1 mp2 : modpath) : bool :=
    match modpath_eq_dec mp1 mp2 with
    | left _ => true
    | right _ => false
    end.

  Definition only_from_module_of (kn_base : kername) :=
    fun (kn : kername) => negb (eq_modpath kn_base.1 kn.1).

  Module Test1.
    Definition anchor := fun x : nat => x.
    Definition CURRENT_MODULE := Eval compute in <%% anchor %%>.1.
    MetaCoq Run (eta_global_env_template
                   false false CURRENT_MODULE
                   p_app_pair_syn.1
                   (KernameSet.singleton <%% Ex1.partial_app_pair %%>)
                   (fun _ => false)
                   (fun _ => false)).
  End Test1.


  Inductive MyInd (A B C : Type) :=
    miCtor : A * A -> B -> C -> True -> MyInd A B C.

  Module Ex2.
    Definition partial_app1 A B n m := let f := miCtor A in f B bool (let n' := @pair A in n' A n n) m true I.
    Definition partial_app2 := let f := partial_app1 in f bool true.
  End Ex2.

  Set Printing Implicit.
  (** Expands the dependencies and adds the corresponding definitions *)
  MetaCoq Run (eta_expand_def
                 true true
                 CURRENT_MODULE
                 (only_from_module_of <%% Ex2.partial_app2 %%>)
                 Ex2.partial_app2).

  (** [partial_app2_expanded] is defined in terms of [partial_app1_expanded] *)
  Print partial_app2_expanded.
  (* partial_app2_expanded =
  let f := fun H H0 : Type => partial_app1_expanded H H0 in f bool true
       : bool -> true -> MyInd bool true bool
   *)

  Inductive MyInd1 (A B C : Type) :=
    | miCtor0 : MyInd1 A B C
    | miCtor1 : A * A -> B -> True -> C -> MyInd1 A B C.

  Definition partial_app3 A B n m :=
    let f := miCtor1 A in f B bool n m I.

  MetaCoq Run (eta_expand_def
                 true true
                 CURRENT_MODULE
                 (only_from_module_of <%% partial_app3 %%>)
                 partial_app3).

  Module Ex3.
  Definition inc_balance (st :  nat × nat) (new_balance : nat)
                 (p : (0 <=? new_balance) = true) :=
    (st.1 + new_balance, st.2).

  Definition partial_inc_balance st i := inc_balance st i.
  End Ex3.
  MetaCoq Run (p <- tmQuoteRecTransp Ex3.partial_inc_balance false ;;
               eta_global_env_template
                 true true
                 CURRENT_MODULE
                 p.1
                 (KernameSet.union
                    (KernameSet.singleton <%% Ex3.inc_balance %%>)
                    (KernameSet.singleton <%% Ex3.partial_inc_balance %%>))
                 (fun kn => eq_kername kn <%% Ex3.inc_balance %%> ||
                            eq_kername kn <%% Ex3.partial_inc_balance %%>)
                 (only_from_module_of <%% Ex3.partial_inc_balance %%>)
              ).

  Module Ex4.
    (* Partially applied constructor of a recursive inductive type *)
    Definition papp_cons {A} (x : A) (xs : list A) := let my_cons := @cons in
                                                      my_cons A x xs.

    MetaCoq Run (eta_expand_def
                 false false
                 <%% @papp_cons %%>.1
                 (only_from_module_of <%% @papp_cons %%>)
                 papp_cons).
  End Ex4.

  Module Ex5.

    (* Mutial inductive *)
    Inductive even : nat -> Type :=
    | even_O : even 0
    | even_S : forall n, odd n -> even (S n)
    with odd : nat -> Type :=
    | odd_S : forall n, even n -> odd (S n).

    Definition papp_odd :=
      let f := odd_S 0 in
      f even_O.

    MetaCoq Run (eta_expand_def
                   false false
                   <%% papp_odd %%>.1
                   (only_from_module_of <%% papp_odd %%>)
                   papp_odd).

    Inductive Expr (Annot : Type) :=
    | eNat : nat -> Expr Annot
    | eFn : string -> Expr Annot -> Expr Annot
    | eAnnot : Annot -> Expr Annot
    | eApp : Expr Annot -> Exprs Annot -> Expr Annot
    with Exprs (Annot : Type) :=
    | eNil : Exprs Annot
    | eCons : Expr Annot -> Exprs Annot -> Exprs Annot.

    Definition papp_expr :=
      let part_app := eApp _ (eFn unit "f" (eNat unit 0)) in
      part_app (eCons _ (eNat unit 0) (eNil _)).

    MetaCoq Run (eta_expand_def
                   false false
                   <%% papp_expr %%>.1
                   (only_from_module_of <%% papp_expr %%>)
                   papp_expr).
  End Ex5.

End Examples.

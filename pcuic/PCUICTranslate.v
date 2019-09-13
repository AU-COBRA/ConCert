Require Import String List.
From MetaCoq.PCUIC Require Import PCUICAst PCUICLiftSubst.
From MetaCoq.Template Require Import BasicAst utils monad_utils.
Require Import Contraver.Ast.

Module P := PCUICAst.
Import MonadNotation.
Import ListNotations.

(** Translation of types to MetaCoq terms. Universal types become Pi-types with the first argument being of type [Set]. Keeping them in [Set] is crucial, since we don't have to deal with universe levels *)
Fixpoint type_to_term (ty : type) : term :=
  match ty with
  | tyInd i => tInd (mkInd i 0) []
  | tyForall nm ty => tProd (nNamed nm) (tSort Universe.type0) (type_to_term ty)
  | tyVar nm => tVar nm
  | tyApp ty1 ty2 => mkApps (type_to_term ty1) [type_to_term  ty2]
  | tyArr ty1 ty2 =>
    (* NOTE: we have to lift indices for the codomain,
       since in Coq arrows are Pi types and introduce an binder *)
    tProd nAnon (type_to_term ty1) (lift0 1 (type_to_term ty2))
  | tyRel i => tRel i
  end.

Definition pat_to_lam (body : term)
          :  list term -> list (BasicTC.ident * term) -> term :=
  (fix rec ty_params tys :=
    match tys with
      [] => body
    | (n,ty) :: tys' =>
      (* NOTE: we need to substitute the parameters into the type of each lambda representing a pattern binder. Since each lambda introduces a binder, we need also to lift free variables in [ty_params] *)
      let lam_type := subst ty_params 0 ty in
      tLambda (BasicTC.nNamed n) lam_type (rec (map (lift0 1) ty_params) tys')
    end).

(** Resolves a pattern by looking up in the global environment and returns an index of the constructor in the list of constructors for the given inductive and a list of pairs mapping pattern variable names to the types of the constructor arguments *)
Definition resolve_pat_arity (Σ : global_env) (ind_name : ename) (p : pat)
  : nat * list (ename * type) :=
  (* NOTE: if lookup fails, we return a dummy value [(0,("",[]))]
     to make the function total *)
  let o_ci := resolve_constr Σ ind_name p.(pName) in
  let (i, nm_tys) := from_option o_ci (0,[]) in
  (i, combine p.(pVars) nm_tys).

(** Translating branches of the [eCase] construct. Note that MetaCoq uses indices to represent constructors. Indices are corresponding positions in the list of constructors for a particular inductive type *)
Definition trans_branch (params : list type)(bs : list (pat * term))
           (c : constr) :=
  let nm  := fst c in
  let tys := remove_proj c in
  let tparams := map type_to_term params in
  let o_pt_e := find (fun x =>(fst x).(pName) =? nm) bs in
  let dummy := (0, tVar (nm ++ ": not found")%string) in
  match o_pt_e with
    | Some pt_e => if (Nat.eqb #|(fst pt_e).(pVars)| #|tys|) then
                    let vars_tys := combine (fst pt_e).(pVars) (map type_to_term tys) in
                    (length (fst pt_e).(pVars), pat_to_lam (snd pt_e) (List.rev tparams) vars_tys)
                  else (0, tVar (nm ++ ": arity does not match")%string)
    | None => dummy
  end.

Definition fun_prod {A B C D} (f : A -> C) (g : B -> D) : A * B -> C * D :=
  fun x => (f (fst x), g (snd x)).

Open Scope list.

Fixpoint decompose_inductive (ty : type) : option (ename * list type) :=
  match ty with
  | tyInd x => Some (x,[])
  | tyForall nm ty => None
  | tyApp ty1 ty2 => res <- decompose_inductive ty1;;
                     let '(ind, tys) := res in
                     Some (ind, tys++[ty2])
  | tyVar x => None
  | tyRel x => None
  | tyArr x x0 => None
  end.


(** ** Translation of Oak to MetaCoq *)

Definition expr_to_term (Σ : global_env) : expr -> P.term :=
  fix expr_to_term e :=
  match e with
  | eRel i => tRel i
  | eVar nm => tVar nm
  | eLambda nm ty b => tLambda (nNamed nm) (type_to_term ty) (expr_to_term b)
  | eTyLam nm b => tLambda (nNamed nm) (tSort Universe.type0) (expr_to_term b)
  | eLetIn nm e1 ty e2 => tLetIn (nNamed nm) (expr_to_term e1) (type_to_term ty) (expr_to_term e2)
  | eApp e1 e2 => mkApps (expr_to_term e1) [expr_to_term e2]
  | eConstr i t => match (resolve_constr Σ i t) with
                  | Some c => tConstruct (mkInd i 0) (fst c) []
                  (* NOTE: a workaround to make the function total *)
                  | None => tConstruct (mkInd (i ++ ": no declaration found.") 0) 0 []
                     end
  | eConst nm => tConst nm []
  | eCase nm_i ty2 e bs =>
    let (ty1,i) := nm_i in
    let (nm, tys) := from_option (decompose_inductive ty1) ("Case : not inductive", [tyVar ""]) in
    let typeInfo := tLambda nAnon (type_to_term ty1) (type_to_term ty2) in
    let (_,cs) := from_option (resolve_inductive Σ nm) (0,[(nm ++ "not found",[])%string]) in
    let tbs := map (fun_prod id expr_to_term) bs in
    let branches := map (trans_branch tys tbs) cs in
    tCase (mkInd nm 0, i) typeInfo (expr_to_term e) branches
  | eFix nm nv ty1 ty2 b =>
    let tty1 := type_to_term ty1 in
    let tty2 := type_to_term ty2 in
    let ty := tProd nAnon tty1 tty2 in
    (* NOTE: we have to lift the indices in [tty1] *)
    let body := tLambda (nNamed nv) (lift0 1 tty1) (expr_to_term b) in
    tFix [(mkdef _ (nNamed nm) ty body 0)] 0
  | eTy ty => type_to_term ty
  end.


(** * Translating inductives *)

Import Basics.

Definition of_ename (e : option ename) : BasicTC.name :=
  match e with
  | Some e' => BasicTC.nNamed e'
  | None => BasicTC.nAnon
  end.

(** Translation of constructors of parameterised inductive types requires
    non-trivial manipulation of De Bruijn indices. *)
Definition mkArrows_rec (ind_name : ename) (nparam : nat)  :=
  fix rec (n : nat) (proj_tys : list (option ename * type)) :=
  match proj_tys with
  | [] => (* this is a return type of the constructor *)
    mkApps (tRel (n + nparam)) (map tRel (rev (seq n nparam)))
  | (proj, ty) :: tys' =>
    let res :=
        match ty with
        | tyInd nm => if eqb nm ind_name then
                       tRel n else type_to_term ty
        | tyApp ty1 ty2 =>
          match (decompose_inductive ty1) with
          | Some (nm, tys) =>
            if eqb nm ind_name then
              mkApps (tRel (n+nparam)) (map (compose (lift0 n) type_to_term)
                                 (tys ++ [ty2])) else type_to_term ty
          | None => type_to_term ty
          end
        | tyRel i => tRel (i+n)
        | _ => type_to_term ty (* TODO: check how it works for other
          type constructors applied to parameters of inductive *)
        end in tProd (of_ename proj) res (rec (1+n) tys')
  end.

Definition mkArrows indn nparam := mkArrows_rec indn nparam 0.

Definition trans_one_constr (ind_name : ename) (nparam : nat) (c : constr) : term :=
  let (ctor_name, tys) := c in mkArrows ind_name nparam tys.

Fixpoint gen_params n := match n with
                         | O => []
                         | S n' => let nm := ("A" ++ utils.string_of_nat n)%string in
                                  let decl := LocalAssum (tSort Universe.type0) in
                                  gen_params n' ++ [(nm,decl)]
                         end.

Definition trans_global_dec (gd : global_dec) : mutual_inductive_entry :=
  match gd with
  | gdInd nm nparam cs r =>
    let oie := {|
          mind_entry_typename := nm;
          mind_entry_arity := tSort Universe.type0;
          mind_entry_template := false;
          mind_entry_consnames := map fst cs;
          mind_entry_lc := map (trans_one_constr nm nparam) cs |}
    in
   {| mind_entry_record := if r then (Some (Some nm)) else None;
      mind_entry_finite := if r then BiFinite else Finite;
      mind_entry_params := gen_params nparam;
      mind_entry_inds := [oie];
      mind_entry_universes := Monomorphic_ctx ContextSet.empty;
      mind_entry_private := None;|}
  end.

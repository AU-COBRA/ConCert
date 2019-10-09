Require Import String List.
From MetaCoq.PCUIC Require Import PCUICAst PCUICLiftSubst.
From MetaCoq.Template Require Import BasicAst utils monad_utils.
From ConCert Require Import Ast Notations.

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

(** ** Translation of Oak to MetaCoq *)

Definition expr_to_term (Σ : global_env) : expr -> term :=
fix expr_to_term e :=
  match e with
  | eRel i => tRel i
  | eVar nm => tVar nm
  | eLambda nm ty b => tLambda (nNamed nm) (type_to_term ty) (expr_to_term b)
  | eTyLam nm b => tLambda (nNamed nm) (tSort Universe.type0) (expr_to_term b)
  | eLetIn nm e1 ty e2 => tLetIn (nNamed nm) (expr_to_term e1) (type_to_term ty) (expr_to_term e2)
  | eApp e1 e2 => mkApps (expr_to_term e1) [expr_to_term e2]
  | eConstr i t => match (resolve_constr Σ i t) with
                  | Some c => tConstruct (mkInd i 0) (c.1.2) []
                  (* NOTE: a workaround to make the function total *)
                  | None => tConstruct (mkInd (i ++ ": no declaration found.") 0) 0 []
                     end
  | eConst nm => tConst nm []
  | eCase nm_i ty2 e bs =>
    let (nm, params) := nm_i in
    let typeInfo := tLambda nAnon (mkApps (tInd (mkInd nm 0) [])
                                          (map type_to_term params))
                            (lift0 1 (type_to_term ty2)) in
    match (resolve_inductive Σ nm) with
    | Some v =>
      if Nat.eqb (fst v) #|params| then
        let cs := snd v in
        let tbs := map (fun_prod id expr_to_term) bs in
        let branches := map (trans_branch params tbs) cs in
        tCase (mkInd nm 0, fst v) typeInfo (expr_to_term e) branches
      else tVar "Case: number of params doesn't match with the definition"
    | None => tVar (nm ++ "not found")%string
    end
  | eFix nm nv ty1 ty2 b =>
    let tty1 := type_to_term ty1 in
    let tty2 := type_to_term ty2 in
    let ty := tProd nAnon tty1 (lift0 1 tty2) in
    (* NOTE: we have to lift the indices in [tty1] because [tRel 0] corresponds to the recursive call *)
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
          type constructors applied to parameters of the inductive *)
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

(** A "library" of data types available by default *)

Module BaseTypes.
  Definition Nat_name := "Coq.Init.Datatypes.nat".
  Definition Nat := Nat_name.

  Definition Bool_name := "Coq.Init.Datatypes.bool".
  Definition Bool := Bool_name.

  Definition Unit := "Coq.Init.Datatypes.unit".

End BaseTypes.

Module StdLib.
  Import BaseTypes.

  Definition Σ : global_env :=
    [gdInd Unit 0 [("Coq.Init.Datatypes.tt", [])] false;
      gdInd Bool 0 [("true", []); ("false", [])] false;
      gdInd Nat 0 [("Z", []); ("Suc", [(None,tyInd Nat)])] false;
      gdInd "list" 1 [("nil", []); ("cons", [(None,tyRel 0);
                                               (None,tyApp (tyInd "list") (tyRel 0))])] false;
      gdInd "prod" 2 [("pair", [(None,tyRel 1);(None,tyRel 0)])] false].

  Notation "a + b" := [| {eConst "Coq.Init.Nat.add"} {a} {b} |]
                        (in custom expr at level 0).
  Notation "a * b" := [| {eConst "Coq.Init.Nat.mul"} {a} {b} |]
                        (in custom expr at level 0).
  Notation "a - b" := [| {eConst "Coq.Init.Nat.sub"} {a} {b} |]
                        (in custom expr at level 0).
  Notation "a == b" := [| {eConst "PeanoNat.Nat.eqb"} {a} {b} |]
                         (in custom expr at level 0).
  Notation "a < b" := [| {eConst "PeanoNat.Nat.ltb"} {a} {b} |]
                        (in custom expr at level 0).
  Notation "a <= b" := [| {eConst "PeanoNat.Nat.leb"} {a} {b} |]
                        (in custom expr at level 0).
  Notation "'Zero'" := (eConstr Nat "Z") ( in custom expr at level 0).
  Notation "'Suc'" := (eConstr Nat "Suc") ( in custom expr at level 0).
  Notation "0" := [| Zero |] ( in custom expr at level 0).
  Notation "1" := [| Suc Zero |] ( in custom expr at level 0).

  Notation "'Zero'" := (pConstr "Z" [])
                  (in custom pat at level 0).

  Notation "'Suc' x" := (pConstr "Suc" [x])
                    (in custom pat at level 0,
                        x constr at level 4).

  Notation "a && b" := [| {eConst "andb"} {a} {b} |]
                         (in custom expr at level 0).
  Notation "~ a" := [| {eConst "negb"} {a} |]
                        (in custom expr at level 0).

  Definition true_name := "true".
  Definition false_name := "false".
  Notation "'True'" := (pConstr true_name []) (in custom pat at level 0).
  Notation "'False'" := (pConstr false_name []) ( in custom pat at level 0).

  Notation "'Nil'" := (pConstr "nil" []) (in custom pat at level 0).
  Notation "'Cons' y z" := (pConstr "cons" [y;z])
                             (in custom pat at level 0,
                                 y constr at level 4,
                                 z constr at level 4).


  Notation "'True'" := (eConstr Bool true_name) (in custom expr at level 0).
  Notation "'False'" := (eConstr Bool false_name) ( in custom expr at level 0).

  Notation "'star'" :=
    (eConstr Unit "Coq.Init.Datatypes.tt")
      (in custom expr at level 0).

End StdLib.

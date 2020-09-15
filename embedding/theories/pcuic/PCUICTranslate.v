(** * Translation from λsmart expressions to PCUIC terms *)
Require ZArith.
Require Import String List.
From MetaCoq.PCUIC Require Import PCUICAst PCUICLiftSubst.
From MetaCoq.Template Require Import BasicAst utils monad_utils MCString Loader.
From ConCert.Embedding Require Import Ast Notations Misc MyEnv.
From ConCert.Extraction Require StringExtra.

Module P := PCUICAst.
Import MonadNotation.
Import ListNotations.

(** ** Translation of types *)

Reserved Notation "T⟦ ty ⟧ " (at level 5).

Fixpoint mdots (prefix : modpath) (l : list string) :=
  match l with
  | [] => prefix
  | h :: tl => mdots (MPdot prefix h) tl
  end.

(** Parses a string containig a file path and a module path separated in a way that helps to recover the kername structure.
 E.g. "Path/To/File#ModuleName.NestedModuleName" *)
Definition modpath_of_string (s : string) : modpath:=
  let fpath_mod := StringExtra.str_split "#" s in
  let fpath := hd "" fpath_mod in
  let mod := hd "" (tl fpath_mod) in
  let fpath_items := rev (StringExtra.str_split "/" fpath) in
  let mod_items := StringExtra.str_split "." mod in
  let fp := MPfile fpath_items in
  if mod =? "" then fp
  else mdots fp mod_items.

(** Parses a string containig a file path, a module path separated and a name in a way that helps to recover the kername structure.
 E.g. "Path/To/File#ModuleName.NestedModuleName@FunctionName" *)
Definition kername_of_string (s : string) : kername :=
  let qualified_name := StringExtra.str_split "@" s in
  if Nat.eqb (length qualified_name) 1
  then (* unqualified name was given*)
    (MPfile [], (hd "" qualified_name))
  else let path := hd "" qualified_name in
       let name := hd "" (tl qualified_name) in
       (modpath_of_string path, name).

(** The priting functions below are similar to the ones from MetaCoq, but we use different separators for different parts of the [kername] *)

Definition string_of_dirpath (dp : dirpath) : string :=
  String.concat "/" (rev dp).

Fixpoint string_of_modpath (mp : modpath) : string :=
  match mp with
  | MPfile dp => string_of_dirpath dp
  | MPbound dp id _ =>
    (* currently not supported by the parser *)
    (string_of_dirpath dp ++ "$" ++ id)%string
  | MPdot mp0 id =>
    match mp0 with
    | MPfile _ => (string_of_modpath mp0 ++ "#" ++ id)%string
    | _ => (string_of_modpath mp0 ++ "." ++ id)%string
    end
  end.

Definition string_of_kername (kn : kername) :=
  (string_of_modpath kn.1 ++ "@" ++ kn.2)%string.

(** Translation of types to PCUIC terms. Universal types become Pi-types with the first argument being of type [Set]. Keeping them in [Set] is crucial, since we don't have to deal with universe levels *)
Fixpoint type_to_term (ty : type) : term :=
  match ty with
  | tyInd i => tInd (mkInd (kername_of_string i) 0) []
  | tyForall nm ty => tProd (nNamed nm) (tSort Universe.type0) T⟦ty⟧
  | tyVar nm => tVar nm
  | tyApp ty1 ty2 => tApp T⟦ty1⟧ T⟦ty2⟧
  | tyArr ty1 ty2 =>
    (* NOTE: we have to lift indices for the codomain,
       since in Coq arrows are Pi types and introduce an binder *)
    tProd nAnon T⟦ty1⟧ (lift0 1 T⟦ty2⟧)
  | tyRel i => tRel i
  end
where "T⟦ ty ⟧ " := (type_to_term ty).

(** Translating patterns to iterated lambdas *)
Definition pat_to_lam (body : term)
          :  list term -> list (BasicTC.ident * term) -> term :=
  (fix rec ty_params tys :=
    match tys with
      [] => body
    | (n,ty) :: tys' =>
      (* NOTE: we need to substitute the parameters into the type of
      each lambda representing a pattern binder. Since each lambda
      introduces a binder, we need also to lift free variables in
      [ty_params] *)
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

Open Scope list.


(** ** Translation of expressions *)

Reserved Notation "t⟦ e ⟧ Σ" (at level 5).

Fixpoint expr_to_term (Σ : global_env) (e : expr) : term :=
  match e with
  | eRel i => tRel i
  | eVar nm => tVar nm
  | eLambda nm ty b => tLambda (nNamed nm) T⟦ty⟧ t⟦b⟧Σ
  | eTyLam nm b => tLambda (nNamed nm) (tSort Universe.type0) t⟦b⟧Σ
  | eLetIn nm e1 ty e2 => tLetIn (nNamed nm) t⟦e1⟧Σ T⟦ty⟧ t⟦e2⟧Σ
  | eApp e1 e2 => tApp t⟦e1⟧Σ t⟦e2⟧Σ
  | eConstr i t =>
    match (resolve_constr Σ i t) with
    | Some c => tConstruct (mkInd (kername_of_string i) 0) (c.1.2) []
    | None => tConstruct (mkInd (kername_of_string (i ++ ":no_declaration_found")) 0) 0 []
    end
  | eConst nm => tConst (kername_of_string nm) []
  | eCase nm_i ty2 e bs =>
    let (nm, params) := nm_i in
    let typeInfo := tLambda nAnon (mkApps (tInd (mkInd (kername_of_string nm) 0) [])
                                          (map type_to_term params))
                            (lift0 1 (type_to_term ty2)) in
    match (resolve_inductive Σ nm) with
    | Some v =>
      if Nat.eqb (fst v) #|params| then
        let cs := snd v in
        let tbs := map (fun_prod id (expr_to_term Σ)) bs in
        let branches := map (trans_branch params tbs) cs in
        tCase (mkInd (kername_of_string nm) 0, fst v) typeInfo t⟦e⟧Σ branches
      else tVar "Case: number of params doesn't match with the definition"
    | None => tVar (nm ++ "not found")%string
    end
  | eFix nm nv ty1 ty2 b =>
    let tty1 := T⟦ty1⟧ in
    let tty2 := T⟦ty2⟧ in
    let ty := tProd nAnon tty1 (lift0 1 tty2) in
    (* NOTE: we have to lift the indices in [tty1] because [tRel 0]
             corresponds to the recursive call *)
    let body := tLambda (nNamed nv) (lift0 1 tty1) t⟦b⟧Σ in
    tFix [(mkdef _ (nNamed nm) ty body 0)] 0
  | eTy ty => T⟦ty⟧
  end
where "t⟦ e ⟧ Σ":= (expr_to_term Σ e).


(** * Translation of inductives *)

Import Basics.

Definition of_ename (e : option ename) : BasicTC.name :=
  match e with
  | Some e' =>
    let (mp,unqualified_nm) := kername_of_string e' in
    BasicTC.nNamed unqualified_nm
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
                         | S n' => let nm := ("A" ++ string_of_nat n)%string in
                                  let decl := LocalAssum (tSort Universe.type0) in
                                  gen_params n' ++ [(nm,decl)]
                         end.

Definition trans_global_dec (gd : global_dec) : mutual_inductive_entry :=
  match gd with
  | gdInd nm nparam cs r =>
    let (mp,unqualified_nm) := kername_of_string nm in
    let oie := {|
          mind_entry_typename := unqualified_nm;
          mind_entry_arity := tSort Universe.type0;
          mind_entry_template := false;
          mind_entry_consnames :=
            map (fun c => let (mp,unqualified_nm) := kername_of_string c.1 in
                         unqualified_nm) cs;
          mind_entry_lc := map (trans_one_constr nm nparam) cs |}
    in
   {| mind_entry_record := if r then (Some (Some unqualified_nm)) else None;
      mind_entry_finite := if r then BiFinite else Finite;
      mind_entry_params := gen_params nparam;
      mind_entry_inds := [oie];
      mind_entry_universes := Monomorphic_ctx ContextSet.empty;
      mind_entry_private := None;|}
  end.

(** Extracts a constant name, inductive name or returns None *)
(* TODO: move to utils *)
Definition to_kername (t : Ast.term) : option kername :=
  match t with
  | Ast.tConst c _ => Some c
  | Ast.tInd c _ => Some c.(inductive_mind)
  | _ => None
  end.
(* TODO: move to utils *)
Definition to_string_name (t : Ast.term) : string :=
  match to_kername t with
  | Some kn => string_of_kername kn
  | None => "Not a constant or inductive"
  end.

Example qualified_bool : to_string_name (<% bool %>) = "Coq/Init/Datatypes@bool".
Proof. reflexivity. Qed.

Fixpoint add_prefix_ty (ty : type) (ps : env string) :=
  match ty with
  | tyInd nm =>
    let p := Ast.from_option (lookup ps nm) "" in
    tyInd (p ++ nm)%string
  | tyForall nm ty1 => tyForall nm (add_prefix_ty ty1 ps)
  | tyApp ty1 ty2 => tyApp (add_prefix_ty ty1 ps) (add_prefix_ty ty2 ps)
  | tyVar _ | tyRel _ => ty
  | tyArr ty1 ty2 => tyArr (add_prefix_ty ty1 ps) (add_prefix_ty ty2 ps)
  end.

Fixpoint add_prefix (e : expr) (ps : env string) :=
  match e with
  | eRel _ | eVar _ => e
  | eLambda nm ty e1 => eLambda nm (add_prefix_ty ty ps) (add_prefix e1 ps)
  | eTyLam nm e1 => eTyLam nm (add_prefix e1 ps)
  | eLetIn nm e1 ty e2  => eLetIn nm (add_prefix e1 ps)
                                 (add_prefix_ty ty ps)
                                 (add_prefix e2 ps)
  | eApp e1 e2 => eApp (add_prefix e1 ps) (add_prefix e2 ps)
  | eConstr ind_nm ctor_nm =>
    let p := Ast.from_option (lookup ps ind_nm) "" in
    eConstr (p ++ ind_nm)%string ctor_nm
  | eConst nm =>
    let p := Ast.from_option (lookup ps nm) "" in
    eConst (p ++ nm)%string
  | eCase (ind_nm, tys) ty e1 brs =>
    let p := Ast.from_option (lookup ps ind_nm) "" in
    eCase ((p ++ ind_nm)%string, map (fun ty => add_prefix_ty ty ps) tys)
          (add_prefix_ty ty ps)
          (add_prefix e1 ps)
          (map (on_snd (fun e => add_prefix e ps)) brs)
  | eFix fix_nm nm ty1 ty2 e1 =>
    eFix fix_nm nm
         (add_prefix_ty ty1 ps)
         (add_prefix_ty ty2 ps)
         (add_prefix e1 ps)
  | eTy ty => eTy (add_prefix_ty ty ps)
  end.

Definition add_prefix_gd (gd : global_dec) (ps : env string) :=
  match gd with
  | gdInd nm i ctors b =>
    let p := Ast.from_option (lookup ps nm) "" in
    let ctors' :=
        map (fun '(c_nm, tys) =>
               (c_nm, map (on_snd (fun ty => add_prefix_ty ty ps)) tys)) ctors in
    gdInd (p ++ nm)%string i ctors' b
  end.

Definition add_prefix_genv (Σ : Ast.global_env) (ps : env string) :=
  map (fun x => add_prefix_gd x ps) Σ.

(** A "library" of data types available by default *)

Module BaseTypes.
  Definition Nat_name := to_string_name <% nat %>.
  Definition Nat := Nat_name.

  Definition Bool_name := to_string_name <% bool %>.
  Definition Bool := Bool_name.

  Definition List_name := to_string_name <% list %>.
  Definition List := List_name.

  Definition Prod_name := to_string_name <% prod %>.
  Definition Prod := Prod_name.

  Definition Unit_name := to_string_name <% unit %>.
  Definition Unit := Unit_name.

  Definition String_name := to_string_name <% string %>.
  Definition String := String_name.

  Import ZArith.
  Definition Int_name := to_string_name <% Z %>.
  Definition Int := Int_name.

End BaseTypes.

Module StdLib.
  Import BaseTypes.

  Definition Σ : global_env :=
    [gdInd Unit 0 [("tt", [])] false;
     gdInd Bool 0 [("true", []); ("false", [])] false;
     gdInd Nat 0 [("Z", []); ("Suc", [(None,tyInd Nat)])] false;
     gdInd Int 0 [("Z0", [])] false ; (* we ommit other construtors for now, since in general integer literals are not supported yet *)
     gdInd String 0 [] false; (* just for remapping string to Coq string, construtors are not necessary  *)
     gdInd List 1 [("nil", []); ("cons", [(None,tyRel 0);
                                         (None,tyApp (tyInd List) (tyRel 0))])] false;
     gdInd Prod 2 [("pair", [(None,tyRel 1);(None,tyRel 0)])] false].

  Notation "a + b" := [| {eConst (to_string_name <% Nat.add %>)} {a} {b} |]
                        (in custom expr at level 0).
  Notation "a * b" := [| {eConst (to_string_name <% Nat.mul %>)} {a} {b} |]
                        (in custom expr at level 0).
  Notation "a - b" := [| {eConst (to_string_name <% Nat.sub %>)} {a} {b} |]
                        (in custom expr at level 0).
  Notation "a == b" := [| {eConst (to_string_name <% Nat.eqb %>)} {a} {b} |]
                         (in custom expr at level 0).
  Notation "a < b" := [| {eConst (to_string_name <% Nat.ltb %>)} {a} {b} |]
                        (in custom expr at level 0).
  Notation "a <= b" := [| {eConst (to_string_name <% Nat.leb %>)} {a} {b} |]
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

  Notation "a && b" := [| {eConst (to_string_name <% andb %>)} {a} {b} |]
                         (in custom expr at level 0).
  Notation "~ a" := [| {eConst (to_string_name <% negb %>)} {a} |]
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

Require Import Bool.
Require Import String List.

Require Import MetaCoq.Template.All.
(* TODO: we use definition of monads from Template Coq,
   but (as actually comment in the [monad_utils] says, we
   should use a real monad library) *)
Require Import MetaCoq.Template.monad_utils.

Require Import MyEnv Ast.

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

Definition lpat_to_lam : term -> list term -> list (BasicTC.ident * term) -> term
  := fix rec body ty_params tys :=
       match tys with
         [] => body
       | (n,ty) :: tys' =>
         (* NOTE: we need to substitute the parameters into the type of each lambda representing a pattern binder. Since each lambda introduces a binder, we need also to lift free variables in [ty_params] *)
         let lam_type := subst (map (lift0 #|tys'|) ty_params) 0 ty in
         rec (tLambda (BasicTC.nNamed n) lam_type body) ty_params tys'
       end.

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

Definition expr_to_term (Σ : global_env) : expr -> Ast.term :=
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
                  | None => tConstruct (mkInd (i ++" or " ++ t ++ " : no declaration found.") 0) 0 []
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
              tApp (tRel (n+nparam)) (map (compose (lift0 n) type_to_term)
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

Definition map_syn :=
  gdInd "AMap" 2 [("ANil", []);
                    ("ACons", [(None,tyRel 1);(None,tyRel 0);
                                 (None,(tyApp (tyApp (tyInd "AMap") (tyRel 1)) (tyRel 0)))])] false.

Make Inductive (trans_global_dec map_syn).

(** A "library" of data types available by default *)

Module BaseTypes.
  Definition Nat_name := "Coq.Init.Datatypes.nat".
  Definition Nat := Nat_name.

  Definition Bool_name := "Coq.Init.Datatypes.bool".
  Definition Bool := Bool_name.

  Definition Unit := "Coq.Init.Datatypes.unit".

End BaseTypes.

Import BaseTypes.

(** * Notations for the deep embeding *)

(** Here we use "custom entries" - a new feature of Coq allowing to define autonomous grammars *)

Open Scope list.

Declare Custom Entry ctor.
Declare Custom Entry global_dec.
Declare Custom Entry expr.
Declare Custom Entry pat.
Declare Custom Entry type.
Declare Custom Entry name_type.


Notation "[! ty !]" := ty (ty custom type at level 2).
Notation "ty" := (tyInd ty) (in custom type at level 2, ty constr at level 3).

Notation "ty1 ty2" := (tyApp ty1 ty2)
                        (in custom type at level 4, left associativity,
                            ty1 custom type,
                            ty2 custom type).


Notation "ty1 -> ty2" := (tyArr ty1 ty2)
                          (in custom type at level 4, right associativity,
                              ty1 custom type,
                              ty2 custom type at level 4).

Notation "'∀' x , ty" := (tyForall x ty)
                         (in custom type at level 4, right associativity,
                             x constr at level 2,
                             ty custom type at level 4).


Notation " ' x " := (tyVar x)
                    (in custom type at level 1,
                        x constr at level 2).

Notation "( x )" := x (in custom type, x at level 2).
Notation "< x >" := x (in custom type, x constr).


Definition ex_type := [! ∀ "A", ∀ "B", "prod" '"A" '"B" !].

Compute ((type_to_term (indexify_type [] ex_type))).

Make Definition ex_type_def := (type_to_term (indexify_type [] ex_type)).

Fixpoint ctor_type_to_list_anon (ty : type) : list (option ename * type) :=
  match ty with
  | tyInd i => [(None,tyInd i)]
  | tyArr ty1 ty2 => ctor_type_to_list_anon ty1 ++ ctor_type_to_list_anon ty2
  | _ => [(None ,ty)] (* TODO : figure out what to do here *)
  end.

Notation " ctor : ty " := (ctor, removelast (ctor_type_to_list_anon ty))
                          (in custom ctor at level 2,
                              ctor constr at level 4,
                              ty custom type at level 4).

(** Unfortunately there are some problems with recursive notations (might go away after the next stable release - 8.10.). So,there are several variants of [data], [record], [case] for different number of cases below *)


(* NOTE: couldn't make this work with the recursive notation *)
(* Notation "'data' ty_nm ':=' c1 | .. | cn ;;" := *)
(*   (gdInd ty_nm (cons c1 .. (cons cn nil) ..)) *)
(*     (in custom global_dec at level 1, *)
(*         ty_nm constr at level 4, *)
(*         c1 custom ctor at level 4, *)
(*         cn custom ctor at level 4). *)


Notation "[\ gd \]" := gd (gd custom global_dec at level 2).

Definition simpl_constr c_nm ty_nm : constr := (c_nm, [(None, tyInd ty_nm)]).

Notation "'data' ty_nm ':=' c1 ;" :=
  (gdInd ty_nm 0 [c1] false)
    (in custom global_dec at level 1,
        ty_nm constr at level 4,
        c1 custom ctor at level 4).

Notation "'data' ty_nm ':=' c1 | c2 ;" :=
  (gdInd ty_nm 0 [c1;c2] false)
    (in custom global_dec at level 1,
        ty_nm constr at level 4,
        c1 custom ctor at level 4,
        c2 custom ctor at level 4).

Notation "'data' ty_nm ':=' c1 | c2 | c3 ;" :=
  (gdInd ty_nm 0 [c1;c2;c3] false)
    (in custom global_dec at level 1,
        ty_nm constr at level 4,
        c1 custom ctor at level 4,
        c2 custom ctor at level 4,
        c3 custom ctor at level 4).

Notation "'data' ty_nm ':=' c1 | c2 | c3 | c4 ;" :=
  (gdInd ty_nm 0 [c1;c2;c3;c4] false)
    (in custom global_dec at level 1,
        ty_nm constr at level 4,
        c1 custom ctor at level 4,
        c2 custom ctor at level 4,
        c3 custom ctor at level 4,
        c4 custom ctor at level 4).

Notation "'data' ty_nm ':=' c1 | c2 | c3 | c4 | c5 ;" :=
  (gdInd ty_nm 0 [c1;c2;c3;c4;c5] false)
    (in custom global_dec at level 1,
        ty_nm constr at level 4,
        c1 custom ctor at level 4,
        c2 custom ctor at level 4,
        c3 custom ctor at level 4,
        c4 custom ctor at level 4,
        c5 custom ctor at level 4).
(* Works, but overlaps with the previous notations *)
(* Notation "'data' ty_nm ':=' c1 | .. | cn ;" := *)
(*   (gdInd ty_nm (cons (simpl_constr c1 ty_nm) .. (cons (simpl_constr cn ty_nm) nil) ..)) *)
(*          (in custom global_dec at level 1, *)
(*              ty_nm constr at level 4, *)
(*              c1 constr at level 4, *)
(*              cn constr at level 4). *)


Definition rec_constr (rec_ctor : ename) (proj_tys : list (option ename * type))
  : string * list (option ename * type) :=
  (rec_ctor, proj_tys).

Definition rec_constrs rec_nm := map (rec_constr rec_nm).

Notation "'record' rec_nm := { pr1 : ty1 }" :=
  (gdInd rec_nm 0 [ rec_constr rec_nm [(Some pr1,ty1)]] true)
    (in custom global_dec at level 1,
        pr1 constr at level 4,
        rec_nm constr at level 4,
        ty1 custom type at level 4).

Notation "'record' rec_nm := rec_ctor { pr1 : ty1 ; pr2 : ty2 }" :=
  (gdInd rec_nm 0 [ rec_constr rec_ctor [(Some pr1,ty1);(Some pr2,ty2)]] true)
    (in custom global_dec at level 1,
        rec_nm constr at level 4,
        rec_ctor constr at level 4,
        pr1 constr at level 4,
        pr2 constr at level 4,
        ty1 custom type at level 4,
        ty2 custom type at level 4).

Notation "'record' rec_nm := rec_ctor { pr1 : ty1 ; pr2 : ty2 ; pr3 : ty3 }" :=
  (gdInd rec_nm 0
         [ rec_constr rec_ctor [(Some pr1,ty1);(Some pr2,ty2);(Some pr3,ty3)]] true)
    (in custom global_dec at level 1,
        rec_nm constr at level 4,
        rec_ctor constr at level 4,
        pr1 constr at level 4,
        pr2 constr at level 4,
        pr3 constr at level 4,
        ty1 custom type at level 4,
        ty2 custom type at level 4,
        ty3 custom type at level 4).

Notation "'record' rec_nm # n := rec_ctor { pr1 : ty1 ; pr2 : ty2 ; pr3 : ty3 ; pr4 : ty4 }" :=
  (gdInd rec_nm n
         [ rec_constr rec_ctor [(Some  pr1,ty1);(Some  pr2,ty2);
                                (Some pr3,ty3);(Some pr4,ty4)]] true)
    (in custom global_dec at level 1,
        rec_nm constr at level 4,
        rec_ctor constr at level 4,
        n constr at level 4,
        pr1 constr at level 4,
        pr2 constr at level 4,
        pr3 constr at level 4,
        pr4 constr at level 4,
        ty1 custom type at level 4,
        ty2 custom type at level 4,
        ty3 custom type at level 4,
        ty4 custom type at level 4).


Notation "'record' rec_nm := rec_ctor { pr1 : ty1 ; pr2 : ty2 ; pr3 : ty3 ; pr4 : ty4 }" :=
  (gdInd rec_nm 0
         [ rec_constr rec_ctor [(Some  pr1,ty1);(Some  pr2,ty2);
                                (Some pr3,ty3);(Some pr4,ty4)]] true)
    (in custom global_dec at level 1,
        rec_nm constr at level 4,
        rec_ctor constr at level 4,
        pr1 constr at level 4,
        pr2 constr at level 4,
        pr3 constr at level 4,
        pr4 constr at level 4,
        ty1 custom type at level 4,
        ty2 custom type at level 4,
        ty3 custom type at level 4,
        ty4 custom type at level 4).

Notation "'record' rec_nm := rec_ctor { pr1 : ty1 ; pr2 : ty2 ; pr3 : ty3 ; pr4 : ty4 ; pr5 : ty5 }" :=
  (gdInd rec_nm 0
         [ rec_constr rec_nm [(Some pr1,ty1);(Some pr2,ty2);
                                (Some pr3,ty3);(Some pr4,ty4);
                                  (Some pr5,ty5)]] true)
    (in custom global_dec at level 1,
        rec_nm constr at level 4,
        rec_ctor constr at level 4,
        pr1 constr at level 4,
        pr2 constr at level 4,
        pr3 constr at level 4,
        pr4 constr at level 4,
        pr5 constr at level 4,
        ty1 custom type at level 4,
        ty2 custom type at level 4,
        ty3 custom type at level 4,
        ty4 custom type at level 4,
        ty5 custom type at level 4).

Notation "'record' rec_nm := rec_ctor { pr1 : ty1 ; pr2 : ty2 ; pr3 : ty3 ; pr4 : ty4 ; pr5 : ty5 ; pr6 : ty6 }" :=
  (gdInd rec_nm 0
         [ rec_constr rec_ctor [(Some pr1,ty1);(Some pr2,ty2);
                                (Some pr3,ty3);(Some pr4,ty4);
                                  (Some pr5,ty5);(Some pr6,ty6)]] true)
    (in custom global_dec at level 1,
        rec_nm constr at level 4,
        rec_ctor constr at level 4,
        pr1 constr at level 4,
        pr2 constr at level 4,
        pr3 constr at level 4,
        pr4 constr at level 4,
        pr5 constr at level 4,
        pr6 constr at level 4,
        ty1 custom type at level 4,
        ty2 custom type at level 4,
        ty3 custom type at level 4,
        ty4 custom type at level 4,
        ty5 custom type at level 4,
        ty6 custom type at level 4).


Notation "[| e |]" := e (e custom expr at level 2).
Notation "^ i " := (eRel i) (in custom expr at level 3, i constr at level 4).

Notation "\ x : ty => b" := (eLambda x ty b)
                              (in custom expr at level 1,
                                  ty custom type at level 2,
                                  b custom expr at level 4,
                                  x constr at level 4).

Notation "\\ A => b" := (eTyLam A b)
                         (in custom expr at level 1,
                             b custom expr at level 4,
                             A constr at level 4).

Notation "'let' x : ty := e1 'in' e2" := (eLetIn x e1 ty e2)
                                           (in custom expr at level 1,
                                               ty custom type at level 2,
                                               e1 custom expr at level 4,
                                               e2 custom expr at level 4,
                                               x constr at level 4).

(* Notation "C x .. y" := (pConstr C (cons x .. (cons y nil) .. )) *)
(*                          (in custom pat at level 1, *)
(*                              x constr at level 4, *)
(*                              y constr at level 4). *)

(* Notation "'case' x : ty 'of'  b1 | .. | bn " := *)
(*   (eCase (ty,0) (tyInd "") x (cons b1 .. (cons bn nil) ..)) *)
(*     (in custom expr at level 1, *)
(*         b1 custom expr at level 4, *)
(*         bn custom expr at level 4, *)
(*         ty constr at level 4). *)

Notation "'case' x : ( ind_nm , params ) 'return' ty2 'of' p1 -> b1 " :=
  (eCase (ind_nm,params) ty2 x [(p1,b1)])
    (in custom expr at level 1,
        p1 custom pat at level 4,
        b1 custom expr at level 4,
        ind_nm constr at level 4,
        params constr at level 4,
        ty2 custom type at level 4).

Notation "'case' x : ty1 # n 'return' ty2 'of' | p1 -> b1 | pn -> bn" :=
  (eCase (ty1,n) ty2 x [(p1,b1);(pn,bn)])
    (in custom expr at level 1,
        p1 custom pat at level 4,
        pn custom pat at level 4,
        b1 custom expr at level 4,
        bn custom expr at level 4,
        n constr at level 4,
        ty1 custom type at level 4,
        ty2 custom type at level 4).

Notation "'case' x : ( ind_nm , params ) 'return' ty2 'of' | p1 -> b1 | p2 -> b2 | p3 -> b3"  :=
  (eCase (ind_nm,params) ty2 x [(p1,b1);(p2,b2);(p3,b3)])
    (in custom expr at level 1,
        p1 custom pat at level 4,
        p2 custom pat at level 4,
        p3 custom pat at level 4,
        b1 custom expr at level 4,
        b2 custom expr at level 4,
        b3 custom expr at level 4,
        ind_nm constr at level 4,
        params constr at level 4,
        ty2 custom type at level 4).

Notation "'case' x : ( ind_nm , params ) 'return' < ty2 > 'of' | p1 -> b1 | p2 -> b2 | p3 -> b3"  :=
  (eCase (ind_nm,params) ty2 x [(p1,b1);(p2,b2);(p3,b3)])
    (in custom expr at level 1,
        p1 custom pat at level 4,
        p2 custom pat at level 4,
        p3 custom pat at level 4,
        b1 custom expr at level 4,
        b2 custom expr at level 4,
        b3 custom expr at level 4,
        ind_nm constr at level 4,
        params constr at level 4,
        ty2 constr at level 4).


Notation "'case' x : ( ind_nm , params ) 'return' ty2 'of' | p1 -> b1 | pn -> bn" :=
  (eCase (ind_nm,params) ty2 x [(p1,b1);(pn,bn)])
    (in custom expr at level 1,
        p1 custom pat at level 4,
        pn custom pat at level 4,
        b1 custom expr at level 4,
        bn custom expr at level 4,
        ind_nm constr at level 4,
        params constr at level 4,
        ty2 custom type at level 4).

Notation "'case' x : ( ind_nm , params ) 'return' < ty2 > 'of' | p1 -> b1 | pn -> bn" :=
  (eCase (ind_nm,params) ty2 x [(p1,b1);(pn,bn)])
    (in custom expr at level 1,
        p1 custom pat at level 4,
        pn custom pat at level 4,
        b1 custom expr at level 4,
        bn custom expr at level 4,
        ind_nm constr at level 4,
        params constr at level 4,
        ty2 constr at level 4).



Notation "x" := (eVar x) (in custom expr at level 0, x constr at level 4).

Notation "t1 t2" := (eApp t1 t2) (in custom expr at level 4, left associativity).

Notation "'fix' fixname ( v : ty1 ) : ty2 := b" := (eFix fixname v ty1 ty2 b)
                                  (in custom expr at level 2,
                                      fixname constr at level 4,
                                      v constr at level 4,
                                      b custom expr at level 4,
                                      ty1 custom type at level 4,
                                      ty2 custom type at level 4).
Notation "( x )" := x (in custom expr, x at level 2).
Notation "{ x }" := x (in custom expr, x constr).


Module StdLib.
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


Section Examples.
  Import StdLib.


  Definition x := "x".
  Definition y := "y".
  Definition z := "z".

  Check [| ^0 |].

  Check [| \x : Nat => y |].

  Definition id_f_syn :=  [| (\x : Nat => ^0) 1 |].

  Make Definition id_f_one := (expr_to_term Σ id_f_syn).
  Example id_f_eq : id_f_one = 1. Proof. reflexivity. Qed.

  (* The same as [id_f_syn], but with named vars *)
  Definition id_f_with_vars := [| (\x : Nat => x) 1 |].

  Make Definition id_f_one' := (expr_to_term Σ (indexify [] id_f_with_vars)).
  Example id_f_eq' : id_f_one' = 1. Proof. reflexivity. Qed.

  Definition simple_let_syn :=
    [|
     \x : Nat =>
       let y : Nat := 1 in ^0
     |].

  Make Definition simple_let := (expr_to_term Σ simple_let_syn).
  Example simple_let_eq : simple_let 1 = 1. Proof. reflexivity. Qed.

  Definition simple_let_with_vars_syn :=
    [|
     \x : Nat =>
       let y : Nat := 1 in y
     |].

  Make Definition simple_let' := (expr_to_term Σ (indexify [] simple_let_with_vars_syn)).
  Example simple_let_eq' : simple_let' 0 = 1. Proof. reflexivity. Qed.


  Definition negb_syn :=
    [|
     \x : Bool =>
            case x : (Bool,[]) return Bool of
            | True -> False
            | False -> True
    |].

  Make Definition negb' := (expr_to_term Σ (indexify [] negb_syn)).

  Example negb'_correct : forall b, negb' b = negb b.
  Proof.
    destruct b;easy.
  Qed.

  Definition myplus_syn :=
    [| \x : Nat => \y : Nat => x + y |].

  Make Definition myplus := (expr_to_term Σ (indexify [] myplus_syn)).

  Definition stupid_case :=
    fun y : Set => fun x : y => fun z : list y =>
                  match z with
                  | [] => x
                  | _ => x
                  end.

  Quote Definition q_stupid_case := Eval compute in stupid_case.
  Quote Recursively Definition q_stupid_case_rec := stupid_case.
  Quote Definition cons_syn := (fun A : Set => cons A).

  Definition case_ex :=
    [| \\y  => \x : 'y =>  \z : "list" 'y =>
           case z : ("list", [tyVar "y"]) return 'y of
           | Nil -> x
           | Cons "hd" "tl" -> x |].

  Compute (expr_to_term Σ (indexify [] case_ex)).

  Make Definition case_ex_def :=  (expr_to_term Σ (indexify [] case_ex)).

  Definition case_ex1 :=
    [| \\y  => \"w" : 'y => \x : 'y =>  \z : "list" 'y =>
           case z : ("list", [tyVar "y"]) return "prod" 'y 'y of
           | Nil -> {eConstr "prod" "pair"} {eTy (tyVar y)} {eTy (tyVar y)} x x
           | Cons "hd" "tl" -> {eConstr "prod" "pair"} {eTy (tyVar y)} {eTy (tyVar y)} "hd" x |].

  Compute (expr_to_term Σ (indexify [] case_ex1)).

  Make Definition case_ex_def1 :=  (expr_to_term Σ (indexify [] case_ex1)).

  Definition case_ex2 :=
    [| \\y => case ({eConstr "list" "nil"} "y") : ("list", [tyVar "y"]) return "list" 'y of
              | Nil -> {eConstr "list" "nil"} "y"
              | Cons "hd" "tl" -> {eConstr "list" "nil"} "y" |].

  Compute indexify [] case_ex2.
  Compute (expr_to_term Σ (indexify [] case_ex2)).

  Make Definition case_ex_def2 :=  (expr_to_term Σ (indexify [] case_ex2)).

End Examples.
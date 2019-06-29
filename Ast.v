(** * AST and translation of Oak to MetaCoq supporting polymorphism *)
Require Template.All.

Require Import Bool.
Require Import Template.Ast Template.AstUtils.
Require Import Template.Typing Template.LiftSubst.
Require Import String List.

Require Import MyEnv.

Import ListNotations.

(* TODO: we use definition of monads from Template Coq,
   but (as actually comment in the [monad_utils] says, we
   should use a real monad library) *)
Require Import Template.monad_utils.
Import MonadNotation.

Module TC := Template.Ast.

(** Aliases *)
Definition name := string.
Definition inductive := string.


Inductive type : Set :=
| tyInd : inductive -> type
| tyForall : name -> type -> type
| tyApp : type -> type -> type
| tyVar : name -> type
| tyRel : nat -> type
| tyArr : type -> type -> type.

Fixpoint ctor_type_to_list_anon (ty : type) : list (TC.name * type) :=
  match ty with
  | tyInd i => [(nAnon,tyInd i)]
  | tyArr ty1 ty2 => ctor_type_to_list_anon ty1 ++ ctor_type_to_list_anon ty2
  | _ => [(nAnon,ty)] (* TODO : figure out what to do here *)
  end.

Record pat := pConstr {pName : name; pVars : list name}.

(** ** Oak AST *)

(** We have both named variables and de Bruijn indices.  Translation to Meta Coq requires indices, while named representation is what we might get from the integration API. We can define relations on type of expressions ensuring that either names are used, or indices, but not both at the same time. *)

(** Note also that AST must be explicitly annotated with types. This is required for the translation to Meta Coq. *)
Inductive expr : Set :=
| eRel       : nat -> expr (*de Bruijn index *)
| eVar       : name -> expr (* named variables *)
| eLambda    : name -> type -> expr -> expr
| eTyLam     : name -> expr -> expr (* abstraction for types *)
| eLetIn     : name -> expr -> type -> expr -> expr
| eApp       : expr -> expr -> expr
| eConstr    : inductive -> name -> expr
| eConst     : name -> expr
| eCase      : (type * nat) (* type of discriminee and number of parameters *) ->
               type ->
               expr (* discriminee *) ->
               list (pat * expr) (* branches *) ->
               expr
| eFix       : name (* of the fix *) -> name (* of the arg *) ->
               type (* of the arg *) -> type (* return type *) -> expr (* body *) -> expr
| eTy        : type -> expr.

(** An induction principle that takes into account nested occurrences of expressions
   in the list of branches for [eCase] *)
Definition expr_ind_case (P : expr -> Prop)
           (Hrel    : forall n : nat, P (eRel n))
           (Hvar    : forall n : name, P (eVar n))
           (Hlam    :forall (n : name) (t : type) (e : expr), P e -> P (eLambda n t e))
           (HtyLam : forall (n : name) (e : expr), P e -> P (eTyLam n e))
           (Hletin  : forall (n : name) (e : expr),
               P e -> forall (t : type) (e0 : expr), P e0 -> P (eLetIn n e t e0))
           (Happ    :forall e : expr, P e -> forall e0 : expr, P e0 -> P (eApp e e0))
           (Hconstr :forall (i : inductive) (n : name), P (eConstr i n))
           (Hconst  :forall n : name, P (eConst n))
           (Hcase   : forall (p : type * nat) (t : type) (e : expr),
               P e -> forall l : list (pat * expr), Forall (fun x => P (snd x)) l ->P (eCase p t e l))
           (Hfix    :forall (n n0 : name) (t t0 : type) (e : expr), P e -> P (eFix n n0 t t0 e))
           (Hty : forall t : type, P (eTy t)) :
  forall e : expr, P e.
Proof.
  refine (fix ind (e : expr) := _ ).
  destruct e.
  + apply Hrel.
  + apply Hvar.
  + apply Hlam. apply ind.
  + apply HtyLam. apply ind.
  + apply Hletin; apply ind.
  + apply Happ;apply ind.
  + apply Hconstr.
  + apply Hconst.
  + apply Hcase. apply ind.
    induction l.
    * constructor.
    * constructor. apply ind. apply IHl.
  + apply Hfix. apply ind.
  + apply Hty.
Defined.

Fixpoint iclosed_n (n : nat) (e : expr) : bool :=
  match e with
  | eRel i => Nat.ltb i n
  | eVar x => false
  | eLambda nm ty b => iclosed_n (1+n) b
  | eTyLam _ b => iclosed_n (1+n) b
  | eLetIn nm e1 ty e2 => iclosed_n n e1 && iclosed_n (1+n) e2
  | eApp e1 e2 => iclosed_n n e1 && iclosed_n n e2
  | eConstr x x0 => true
  | eConst x => true
  | eCase ii ty e bs =>
    let bs'' := List.forallb
                  (fun x => iclosed_n (length ((fst x).(pVars)) + n) (snd x)) bs in
    iclosed_n n e && bs''
  | eFix fixname nm ty1 ty2 e => iclosed_n (2+n) e
  | eTy _ => true (* TODO : think about closed types *)
  end.

Definition vars_to_apps acc vs :=
  fold_left eApp vs acc.

Definition constr := (string * list (TC.name * type))%type.

(** Global declarations. Will be extended to handle declaration of constant, e.g. function definitions *)
Inductive global_dec :=
| gdInd : name
          -> nat (* num of params *)
          -> list constr
          -> bool (* set to [true] if it's a record *)
          -> global_dec.


Definition global_env := list global_dec.

Fixpoint lookup {A} (l : list (string * A)) key : option A :=
  match l with
  | [] => None
  | (key', v) :: xs => if eq_string key' key then Some v else lookup xs key
  end.

Fixpoint lookup_global ( Σ : global_env) key : option global_dec :=
  match Σ with
  | [] => None
  | gdInd key' n v r :: xs => if eq_string key' key then Some (gdInd key' n v r) else lookup_global xs key
  end.

(** Looks up for the given inductive by name and if succeeds, returns a list of constructors with corresponding arities *)
Definition resolve_inductive (Σ : global_env) (ind_name : ident)
  : option (nat * list constr) :=
  match (lookup_global Σ ind_name) with
  | Some (gdInd n nparam cs _) => Some (nparam, cs)
  | None => None
  end.

Definition remove_proj (c : constr) := map snd (snd c).

(** Resolves the given constructor name to a corresponding position in the list of constructors along with the constructor arity *)
Definition resolve_constr (Σ : global_env) (ind_name constr_name : ident)
  : option (nat * list type)  :=
  match (resolve_inductive Σ ind_name) with
  | Some n_cs => lookup_with_ind (map (fun c => (fst c, remove_proj c)) (snd n_cs)) constr_name
  | None => None
  end.

Definition from_option {A : Type} ( o : option A) (default : A) :=
  match o with
  | None => default
  | Some v => v
  end.

Definition bump_indices (l : list (name * nat)) (n : nat) :=
  map (fun '(x,y) => (x, n+y)) l.

(** For a list of vars returns a list of pairs (var,number) where the number is a position of the var counted from the end of the list.
 E.g. number_vars ["x"; "y"; "z"] = [("x", 2); ("y", 1); ("z", 0)] *)
Definition number_vars (i : nat) (ns : list name) : list (name * nat) :=
  combine ns (rev (seq i (length ns + i))).

Example number_vars_xyz : number_vars 0 ["x"; "y"; "z"] = [("x", 2); ("y", 1); ("z", 0)].
Proof. reflexivity. Qed.

(** Converting variable names to De Bruijn indices in types *)
Fixpoint indexify_type (l : list (name * nat)) (ty : type) : type :=
  match ty with
  | tyInd i => tyInd i
  | tyForall nm ty => tyForall nm (indexify_type ((nm,0) :: bump_indices l 1) ty)
  | tyVar nm => match (lookup l nm) with
               | None => (* NOTE: a workaround to make the function total *)
                 tyVar ("not a closed type")
               | Some v => tyRel v
               end
  | tyRel i => tyRel i
  | tyApp ty1 ty2 =>
    tyApp (indexify_type l ty1) (indexify_type l ty2)
  | tyArr ty1 ty2 =>
    (* NOTE: we have to bump indices for the codomain,
       since in Coq arrow also introduces a binder in a MetaCoq term.
       So, this is purely an artifact of the translation to MetaCoq *)
    tyArr (indexify_type l ty1) (indexify_type (bump_indices l 1) ty2)
  end.

(** Converting variable names to De Bruijn indices *)
Fixpoint indexify (l : list (name * nat)) (e : expr) : expr :=
  match e with
  | eRel i => eRel i
  | eVar nm =>
    match (lookup l nm) with
    | None => (* NOTE: a workaround to make the function total *)
      eVar ("not a closed term")
    | Some v => eRel v
    end
  | eLambda nm ty b =>
    eLambda nm (indexify_type l ty) (indexify ((nm,0 ):: bump_indices l 1) b)
  | eTyLam nm b => eTyLam nm (indexify ((nm,0 ):: bump_indices l 1) b)
  | eLetIn nm e1 ty e2 =>
    eLetIn nm (indexify l e1) (indexify_type l ty) (indexify ((nm, 0) :: bump_indices l 1) e2)
  | eApp e1 e2 => eApp (indexify l e1) (indexify l e2)
  | eConstr t i as e => e
  | eConst nm as e => e
  | eCase nm_i ty2 e bs =>
    let (ty1,i) := nm_i in
    eCase (indexify_type l ty1,i)
          (indexify_type (bump_indices l 1) ty2) (indexify l e)
          (map (fun p => (fst p, indexify (number_vars 0 (fst p).(pVars) ++
                               bump_indices l (length (fst p).(pVars))) (snd p))) bs)
  | eFix nm vn ty1 ty2 b =>
    (* NOTE: name of the fixpoint becomes an index as well *)
    let l' := ((nm,1) :: (vn,0) :: bump_indices l 2) in
    (* NOTE: indexifying types is not a very good abstraction anymore.
       [ty2] is needed in the translation in 2 places with different indices,
       so we have to lift the indices in the translation again *)
    let l'' := bump_indices l 1 in
    eFix nm vn (indexify_type l ty1) (indexify_type l'' ty2) (indexify l' b)
  | eTy ty => eTy (indexify_type l ty)
  end.

(** Translation of types to MetaCoq terms. Universal types become Pi-types with the first argument being of type [Set]. Keeping them in [Set] is crucial, since we don't have to deal with universe levels *)
Fixpoint type_to_term (ty : type) : term :=
  match ty with
  | tyInd i => tInd (mkInd i 0) []
  | tyForall nm ty => tProd (nNamed nm) (tSort Universe.type0) (type_to_term ty)
  | tyVar nm => tVar nm
  | tyApp ty1 ty2 => mkApps (type_to_term ty1) [type_to_term  ty2]
  | tyArr ty1 ty2 => tProd nAnon (type_to_term ty1) (type_to_term ty2)
  | tyRel i => tRel i
  end.

Fixpoint iter_lam_type (n : nat) (t : term) :=
  match n with
  | O => t
  | S n' => tLambda nAnon (tSort Universe.type0) (iter_lam_type n' t)
  end.

Definition build_pat_type (tys : list term) t :=
  tApp (iter_lam_type (length tys) t) tys.

Fixpoint pat_to_lam (i : nat)(params : list term) (tys : list (name * type))
         (body : term) : term :=
  match tys with
    [] => body
  | (n,ty) :: tys' =>
    let lam_type := build_pat_type (map (lift0 i) params) (type_to_term ty) in
    tLambda (nNamed n) lam_type (pat_to_lam (i+1) params tys' body)
  end.

Fixpoint pat_to_elam (tys : list (name * type)) (body : expr) : expr :=
  match tys with
    [] => body
  | (n,ty) :: tys' => eLambda n ty (pat_to_elam tys' body)
  end.

(** Resolves a pattern by looking up in the global environment and returns an index of the constructor in the list of constructors for the given inductive and a list of pairs mapping pattern variable names to the types of the constructor arguments *)
Definition resolve_pat_arity (Σ : global_env) (ind_name : name) (p : pat) : nat * list (name * type) :=
  (* NOTE: in lookup failed we return a dummy value [(0,("",[]))]
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
                    let vars_tys := combine (fst pt_e).(pVars) tys in
                    (length (fst pt_e).(pVars), pat_to_lam 0 tparams vars_tys (snd pt_e))
                  else (0, tVar (nm ++ ": arity does not match")%string)
    | None => dummy
  end.

Definition fun_prod {A B C D} (f : A -> C) (g : B -> D) : A * B -> C * D :=
  fun x => (f (fst x), g (snd x)).

Fixpoint decompose_inductive (ty : type) : option (name * list type) :=
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
                  | Some c => tConstruct (mkInd i 0) (fst c) []
                  (* NOTE: a workaround to make the function total *)
                  | None => tConstruct (mkInd (i ++ ": no declaration found.") 0) 0 []
                     end
  | eConst nm => tConst nm []
  | eCase nm_i ty2 e bs =>
    let (ty1,i) := nm_i in
    let (nm, tys) := from_option (decompose_inductive ty1) ("Case : not inductive", [tyVar ""]) in
    let typeInfo := tLambda nAnon (type_to_term ty1)
                            (type_to_term ty2) in
    let (_,cs) := from_option (resolve_inductive Σ nm) (0,[(nm ++ "not found",[])%string]) in
    let tbs := map (fun_prod id expr_to_term) bs in
    let branches := map (trans_branch tys tbs) cs in
    tCase (mkInd nm 0, i) typeInfo (expr_to_term e) branches
  | eFix nm nv ty1 ty2 b =>
    let tty1 := type_to_term ty1 in
    let tty2 := type_to_term ty2 in
    let ty := tProd nAnon tty1 tty2 in
    (* NOTE: we have to lift the indices in [tty2] again, see comments in [indexify]  *)
    let body := tLambda (nNamed nv) (lift0 1 tty1) (expr_to_term b) in
    tFix [(mkdef _ (nNamed nm) ty body 0)] 0
  | eTy ty => type_to_term ty
  end.


(** * Translating inductives *)

(** Note that there is no support for parameterised inductives so far. *)

Import Basics.


(** Translation of constructors of parameterised inductive types requires
    non-trivial manipulation of De Bruijn indices. *)
Definition mkArrows_rec (ind_name : name) (nparam : nat)  :=
  fix rec (n : nat) (proj_tys : list (Template.Ast.name * type)) :=
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
        end in tProd proj res (rec (1+n) tys')
  end.

Definition mkArrows indn nparam := mkArrows_rec indn nparam 0.

Definition trans_one_constr (ind_name : name) (nparam : nat) (c : constr) : term :=
  let (ctor_name, tys) := c in mkArrows ind_name nparam tys.

Fixpoint gen_params n := match n with
                         | O => []
                         | S n' => gen_params n' ++ [mkdecl
                                  (nNamed ("A" ++ utils.string_of_nat n)%string)
                                  None
                                  (tSort Universe.type0)]
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
   {| mind_entry_record := if r then (Some (Some [nm])) else None;
      mind_entry_finite := if r then BiFinite else Finite;
      mind_entry_params := gen_params nparam;
      mind_entry_inds := [oie];
      mind_entry_universes := Monomorphic_ctx ([], ConstraintSet.empty);
      mind_entry_private := None;|}
  end.

Definition map_syn :=
  gdInd "AMap" 2 [("ANil", []);
                    ("ACons", [(nAnon,tyRel 1);(nAnon,tyRel 0);
                                 (nAnon,(tyApp (tyApp (tyInd "AMap") (tyRel 1)) (tyRel 0)))])] false.

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
                        (in custom type at level 4, left associativity).


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

Notation "( x )" := x (in custom type, x custom type at level 2).
Notation "{ x }" := x (in custom type, x constr).


Definition ex_type := [! ∀ "A", ∀ "B", "prod" '"A" '"B" !].

Compute ((type_to_term (indexify_type [] ex_type))).

Make Definition ex_type_def := Eval compute in (type_to_term (indexify_type [] ex_type)).


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

Definition simpl_constr c_nm ty_nm : constr := (c_nm, [(nAnon, tyInd ty_nm)]).

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


Definition rec_constr (rec_nm :name) (proj_tys : list (TC.name * type)) :=
  (("mk"++ rec_nm)%string, proj_tys).

Definition rec_constrs rec_nm := map (rec_constr rec_nm).

Notation "'record' rec_nm := { pr1 : ty1 }" :=
  (gdInd rec_nm 0 [ rec_constr rec_nm [(nNamed pr1,ty1)]] true)
    (in custom global_dec at level 1,
        pr1 constr at level 4,
        rec_nm constr at level 4,
        ty1 custom type at level 4).

Notation "'record' rec_nm := { pr1 : ty1 ; pr2 : ty2 }" :=
  (gdInd rec_nm 0 [ rec_constr rec_nm [(nNamed pr1,ty1);(nNamed pr2,ty2)]] true)
    (in custom global_dec at level 1,
        rec_nm constr at level 4,
        pr1 constr at level 4,
        pr2 constr at level 4,
        ty1 custom type at level 4,
        ty2 custom type at level 4).

Notation "'record' rec_nm := { pr1 : ty1 ; pr2 : ty2 ; pr3 : ty3 }" :=
  (gdInd rec_nm 0
         [ rec_constr rec_nm [(nNamed pr1,ty1);(nNamed pr2,ty2);(nNamed pr3,ty3)]] true)
    (in custom global_dec at level 1,
        rec_nm constr at level 4,
        pr1 constr at level 4,
        pr2 constr at level 4,
        pr3 constr at level 4,
        ty1 custom type at level 4,
        ty2 custom type at level 4,
        ty3 custom type at level 4).

Notation "'record' rec_nm := { pr1 : ty1 ; pr2 : ty2 ; pr3 : ty3 ; pr4 : ty4 }" :=
  (gdInd rec_nm 0
         [ rec_constr rec_nm [(nNamed pr1,ty1);(nNamed pr2,ty2);
                                (nNamed pr3,ty3);(nNamed pr4,ty4)]] true)
    (in custom global_dec at level 1,
        rec_nm constr at level 4,
        pr1 constr at level 4,
        pr2 constr at level 4,
        pr3 constr at level 4,
        pr4 constr at level 4,
        ty1 custom type at level 4,
        ty2 custom type at level 4,
        ty3 custom type at level 4,
        ty4 custom type at level 4).

Notation "'record' rec_nm := { pr1 : ty1 ; pr2 : ty2 ; pr3 : ty3 ; pr4 : ty4 ; pr5 : ty5 }" :=
  (gdInd rec_nm 0
         [ rec_constr rec_nm [(nNamed pr1,ty1);(nNamed pr2,ty2);
                                (nNamed pr3,ty3);(nNamed pr4,ty4);
                                  (nNamed pr5,ty5)]] true)
    (in custom global_dec at level 1,
        rec_nm constr at level 4,
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

Notation "'case' x : ty1 'return' ty2 'of' p1 -> b1 " :=
  (eCase (ty1,0) ty2 x [(p1,b1)])
    (in custom expr at level 1,
        p1 custom pat at level 4,
        b1 custom expr at level 4,
        ty1 custom type at level 4,
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

Notation "'case' x : ty1 'return' ty2 'of' | p1 -> b1 | p2 -> b2 | p3 -> b3"  :=
  (eCase (ty1,0) ty2 x [(p1,b1);(p2,b2);(p3,b3)])
    (in custom expr at level 1,
        p1 custom pat at level 4,
        p2 custom pat at level 4,
        p3 custom pat at level 4,
        b1 custom expr at level 4,
        b2 custom expr at level 4,
        b3 custom expr at level 4,
        ty1 custom type at level 4,
        ty2 custom type at level 4).

Notation "'case' x : ty1 'return' ty2 'of' | p1 -> b1 | pn -> bn" :=
  (eCase (ty1,0) ty2 x [(p1,b1);(pn,bn)])
    (in custom expr at level 1,
        p1 custom pat at level 4,
        pn custom pat at level 4,
        b1 custom expr at level 4,
        bn custom expr at level 4,
        ty1 custom type at level 4,
        ty2 custom type at level 4).



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
      gdInd Nat 0 [("Z", []); ("Suc", [(nAnon,tyInd Nat)])] false;
      gdInd "list" 1 [("Nil", []); ("Cons", [(nAnon,tyRel 0);
                                               (nAnon,tyApp (tyInd "list") (tyRel 0))])] false;
      gdInd "prod" 2 [("Pair", [(nAnon,tyRel 1);(nAnon,tyRel 0)])] false].

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
  Notation "'Z'" := (eConstr Nat "Z") ( in custom expr at level 0).
  Notation "'Suc'" := (eConstr Nat "Suc") ( in custom expr at level 0).
  Notation "0" := [| Z |] ( in custom expr at level 0).
  Notation "1" := [| Suc Z |] ( in custom expr at level 0).

  Notation "'Z'" := (pConstr "Z" [])
                  (in custom pat at level 0).

  Notation "'Suc' x" := (pConstr "Suc" [x])
                    (in custom pat at level 0,
                        x constr at level 4).

  Notation "a && b" := [| {eConst "andb"} {a} {b} |]
                        (in custom expr at level 0).

  Definition true_name := "true".
  Definition false_name := "false".
  Notation "'True'" := (pConstr true_name []) (in custom pat at level 0).
  Notation "'False'" := (pConstr false_name []) ( in custom pat at level 0).

  Notation "'Nil'" := (pConstr "Nil" []) (in custom pat at level 0).
  Notation "'Cons' y z" := (pConstr "Cons" [y;z])
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

  Make Definition id_f_one := Eval compute in (expr_to_term Σ id_f_syn).
  Example id_f_eq : id_f_one = 1. Proof. reflexivity. Qed.

  (* The same as [id_f_syn], but with named vars *)
  Definition id_f_with_vars := [| (\x : Nat => x) 1 |].

  Make Definition id_f_one' := Eval compute in (expr_to_term Σ (indexify [] id_f_with_vars)).
  Example id_f_eq' : id_f_one' = 1. Proof. reflexivity. Qed.

  Definition simple_let_syn :=
    [|
     \x : Nat =>
       let y : Nat := 1 in ^0
     |].

  Make Definition simple_let := Eval compute in (expr_to_term Σ simple_let_syn).
  Example simple_let_eq : simple_let 1 = 1. Proof. reflexivity. Qed.

  Definition simple_let_with_vars_syn :=
    [|
     \x : Nat =>
       let y : Nat := 1 in y
     |].

  Make Definition simple_let' := Eval compute in (expr_to_term Σ (indexify [] simple_let_with_vars_syn)).
  Example simple_let_eq' : simple_let' 0 = 1. Proof. reflexivity. Qed.


  Definition negb_syn :=
    [|
     \x : Bool =>
            case x : Bool #0 return Bool of
            | True -> False
            | False -> True
    |].

  Make Definition negb' := Eval compute in (expr_to_term Σ (indexify [] negb_syn)).

  Example negb'_correct : forall b, negb' b = negb b.
  Proof.
    destruct b;easy.
  Qed.

  Definition myplus_syn :=
    [| \x : Nat => \y : Nat => x + y |].

  Make Definition myplus := Eval compute in (expr_to_term Σ (indexify [] myplus_syn)).

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
           case z : "list" 'y # 1 return 'y of
           | Nil -> x
           | Cons "hd" "tl" -> x |].

  Compute (expr_to_term Σ (indexify [] case_ex)).

  Make Definition case_ex_def := Eval compute in (expr_to_term Σ (indexify [] case_ex)).

  Definition case_ex1 :=
    [| \\y  => \"w" : 'y => \x : 'y =>  \z : "list" 'y =>
           case z : "list" 'y # 1 return "prod" 'y 'y of
           | Nil -> {eConstr "prod" "Pair"} {eTy (tyVar y)} {eTy (tyVar y)} x x
           | Cons "hd" "tl" -> {eConstr "prod" "Pair"} {eTy (tyVar y)} {eTy (tyVar y)} "hd" x |].

  Compute (expr_to_term Σ (indexify [] case_ex1)).

  Make Definition case_ex_def1 := Eval compute in (expr_to_term Σ (indexify [] case_ex1)).


End Examples.
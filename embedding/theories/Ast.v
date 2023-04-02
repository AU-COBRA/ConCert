(** * λsmart language definition *)
From MetaCoq.Template Require All.
From Coq Require Import String.
From Coq Require Import List.
From ConCert.Utils Require Import Env.

Import ListNotations.

Module BasicTC := MetaCoq.Common.BasicAst.
Import Ast.

(** Aliases *)
Definition ename := string.
Definition inductive := string.


Inductive type : Set :=
| tyInd : inductive -> type
| tyForall : ename -> type -> type
| tyApp : type -> type -> type
| tyVar : ename -> type
| tyRel : nat -> type
| tyArr : type -> type -> type.

Record pat := pConstr {pName : ename; pVars : list ename}.

(** ** λsmart AST *)

(** We have both named variables and de Bruijn indices.
    Translation to MetaCoq requires indices, while named representation
    is what we might get from the integration API. We can define relations
    on type of expressions ensuring that either names are used, or indices,
    but not both at the same time. *)

(** Note also that AST must be explicitly annotated with types.
    This is required for the translation to MetaCoq. *)
Inductive expr : Set :=
| eRel       : nat -> expr (* de Bruijn index *)
| eVar       : ename -> expr (* named variables *)
| eLambda    : ename -> type -> expr -> expr
| eTyLam     : ename -> expr -> expr (* abstraction for types *)
| eLetIn     : ename -> expr -> type -> expr -> expr
| eApp       : expr -> expr -> expr
| eConstr    : inductive -> ename -> expr
| eConst     : ename -> expr
| eCase      : (inductive * list type) (* type of discriminee and a list of parameters *) ->
               type ->
               expr (* discriminee *) ->
               list (pat * expr) (* branches *) ->
               expr
| eFix       : ename (* of the fix *) -> ename (* of the arg *) ->
               type (* of the arg *) -> type (* return type *) -> expr (* body *) -> expr
| eTy        : type -> expr.

(** An induction principle that takes into account nested
    occurrences of expressions in the list of branches for [eCase] *)
Definition expr_ind_case (P : expr -> Prop)
           (Hrel    : forall n : nat, P (eRel n))
           (Hvar    : forall n : ename, P (eVar n))
           (Hlam    :forall (n : ename) (t : type) (e : expr), P e -> P (eLambda n t e))
           (HtyLam : forall (n : ename) (e : expr), P e -> P (eTyLam n e))
           (Hletin  : forall (n : ename) (e : expr),
               P e -> forall (t : type) (e0 : expr), P e0 -> P (eLetIn n e t e0))
           (Happ    :forall e : expr, P e -> forall e0 : expr, P e0 -> P (eApp e e0))
           (Hconstr :forall (i : inductive) (n : ename), P (eConstr i n))
           (Hconst  :forall n : ename, P (eConst n))
           (Hcase   : forall (p : inductive * list type) (t : type) (e : expr),
               P e -> forall l : list (pat * expr), Forall (fun x => P (snd x)) l ->P (eCase p t e l))
           (Hfix    :forall (n n0 : ename) (t t0 : type) (e : expr), P e -> P (eFix n n0 t t0 e))
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
  + apply Happ; apply ind.
  + apply Hconstr.
  + apply Hconst.
  + apply Hcase. apply ind.
    induction l.
    * constructor.
    * constructor. apply ind. apply IHl.
  + apply Hfix. apply ind.
  + apply Hty.
Defined.


Fixpoint iclosed_ty (n : nat) (ty : type) : bool :=
  match ty with
  | tyInd x => true
  | tyForall v ty1 => iclosed_ty (1+n) ty1
  | tyApp ty1 ty2 => iclosed_ty n ty1 && iclosed_ty n ty2
  | tyVar _ => false
  | tyRel i => Nat.ltb i n
  | tyArr ty1 ty2 => iclosed_ty n ty1 && iclosed_ty n ty2
  end.

Fixpoint iclosed_n (n : nat) (e : expr) : bool :=
  match e with
  | eRel i => Nat.ltb i n
  | eVar x => false
  | eLambda nm ty b => iclosed_ty n ty && iclosed_n (1+n) b
  | eTyLam _ b => iclosed_n (1+n) b
  | eLetIn nm e1 ty e2 => iclosed_ty n ty && iclosed_n n e1 && iclosed_n (1+n) e2
  | eApp e1 e2 => iclosed_n n e1 && iclosed_n n e2
  | eConstr x x0 => true
  | eConst x => true
  | eCase ii ty e bs =>
    let bs'' := List.forallb
                  (fun x => iclosed_n (length ((fst x).(pVars)) + n) (snd x)) bs in
    forallb (iclosed_ty n) (snd ii) && iclosed_ty n ty && iclosed_n n e && bs''
  | eFix fixname nm ty1 ty2 e => iclosed_ty n ty1 && iclosed_ty n ty2 && iclosed_n (2+n) e
  | eTy ty => iclosed_ty n ty
  end.

Definition vars_to_apps acc vs :=
  fold_left eApp vs acc.

Definition constr := (string * list (option ename * type))%type.

(** Global declarations. Will be extended to handle
    declaration of constant, e.g. function definitions *)
Inductive global_dec :=
| gdInd : ename
          -> nat (* num of params *)
          -> list constr
          -> bool (* set to [true] if it's a record *)
          -> global_dec.


Definition global_env := list global_dec.

Fixpoint lookup {A} (l : list (string * A)) key : option A :=
  match l with
  | [] => None
  | (key', v) :: xs => if eqb key' key then Some v else lookup xs key
  end.

Fixpoint lookup_global ( Σ : global_env) (key : ename) : option global_dec :=
  match Σ with
  | [] => None
  | gdInd key' n v r :: xs => if eqb key' key then Some (gdInd key' n v r) else lookup_global xs key
  end.

(** Looks up for the given inductive by name and if succeeds,
    returns a list of constructors with corresponding arities *)
Definition resolve_inductive (Σ : global_env) (ind_name : ename)
  : option (nat * list constr) :=
  match (lookup_global Σ ind_name) with
  | Some (gdInd n nparam cs _) => Some (nparam, cs)
  | None => None
  end.

Definition remove_proj (c : constr) := map snd (snd c).

(** Resolves the given constructor name to a corresponding position
    in the list of constructors along with the constructor's arity *)
Definition resolve_constr (Σ : global_env) (ind_name constr_name : ename)
  : option (nat * nat * list type) :=
  match (resolve_inductive Σ ind_name) with
  | Some n_cs =>
    match lookup_with_ind (map (fun c => (fst c, remove_proj c)) (snd n_cs)) constr_name with
    | Some v => Some (fst n_cs, fst v, snd v)
    | None => None
    end
  | None => None
  end.

Definition bump_indices (l : list (ename * nat)) (n : nat) :=
  map (fun '(x,y) => (x, n+y)) l.

(** For a list of vars returns a list of pairs (var,number) where
    the number is a position of the var counted from the end of the list.
    E.g. number_vars ["x"; "y"; "z"] = [("x", 2); ("y", 1); ("z", 0)] *)
Definition number_vars (i : nat) (ns : list ename) : list (ename * nat) :=
  combine ns (rev (seq i (length ns + i))).

Open Scope string.

Example number_vars_xyz : number_vars 0 ["x"; "y"; "z"] = [("x", 2); ("y", 1); ("z", 0)].
Proof. reflexivity. Qed.

(** ** Conversion from named representation to De Bruijn indices *)

(** Converting variable names to De Bruijn indices in types *)
Fixpoint indexify_type (l : list (ename * nat)) (ty : type) : type :=
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
    (* tyArr (indexify_type l ty1) (indexify_type (bump_indices l 1) ty2) *)
    tyArr (indexify_type l ty1) (indexify_type l ty2)
  end.

(** Converting variable names to De Bruijn indices *)
Fixpoint indexify (l : list (ename * nat)) (e : expr) : expr :=
  match e with
  | eRel i => eRel i
  | eVar nm =>
    match (lookup l nm) with
    | None => (* NOTE: a workaround to make the function total *)
      eVar ("not a closed term")
    | Some v => eRel v
    end
  | eLambda nm ty b =>
    eLambda nm (indexify_type l ty) (indexify ((nm,0 ) :: bump_indices l 1) b)
  | eTyLam nm b => eTyLam nm (indexify ((nm,0 ) :: bump_indices l 1) b)
  | eLetIn nm e1 ty e2 =>
    eLetIn nm (indexify l e1) (indexify_type l ty) (indexify ((nm, 0) :: bump_indices l 1) e2)
  | eApp e1 e2 => eApp (indexify l e1) (indexify l e2)
  | eConstr t i as e => e
  | eConst nm as e => e
  | eCase nm_i ty2 e bs =>
    let (nm,tys) := nm_i in
    eCase (nm,map (indexify_type l) tys)
          (indexify_type l ty2) (indexify l e)
          (map (fun p => (fst p, indexify (number_vars 0 (fst p).(pVars) ++
                               bump_indices l (length (fst p).(pVars))) (snd p))) bs)
  | eFix nm vn ty1 ty2 b =>
    (* NOTE: name of the fixpoint becomes an index as well *)
    let l' := bump_indices l 2 in
    let l'' := ((nm,1) :: (vn,0) :: l') in
    eFix nm vn (indexify_type l ty1) (indexify_type l ty2) (indexify l'' b)
  | eTy ty => eTy (indexify_type l ty)
  end.

(** Lifting indices of type variables in types *)
Fixpoint lift_type_vars (n k : nat) (ty : type) : type :=
  match ty with
  | tyInd nm => tyInd nm
  | tyForall nm ty => tyForall nm (lift_type_vars n (1+k) ty)
  | tyVar nm => tyVar nm
  | tyRel i => if Nat.leb k i then tyRel (n + i) else tyRel i
  | tyApp ty1 ty2 =>
    tyApp (lift_type_vars n k ty1) (lift_type_vars n k ty2)
  | tyArr ty1 ty2 =>
    tyArr (lift_type_vars n k ty1) (lift_type_vars n k ty2)
  end.

(** ** Merging type and term De Bruijn indices *)

(** Merging De Bruijn indices of type variables corresponding to type
    abstractions with lambda abstractions. We assume that the expressions
    are in the prenex form, so type abstractions can only occur at
    the outermost positions: [\\A => \\ B => ... \x => \y => t] *)
Fixpoint reindexify (n : nat) (e : expr) : expr :=
  match e with
  | eRel i => eRel i
  | eVar nm => eVar ("Named variables are not supported")
  | eLambda nm ty b =>
    eLambda nm (lift_type_vars n 0 ty) (reindexify (1+n) b)
  | eTyLam nm b =>
    (* we do not increment [n] since we assume prenex form *)
    eTyLam nm (reindexify n b)
  | eLetIn nm e1 ty e2 =>
    eLetIn nm (reindexify n e1) (lift_type_vars n 0 ty) (reindexify (1+n) e2)
  | eApp e1 e2 => eApp (reindexify n e1) (reindexify n e2)
  | eConstr t i as e => e
  | eConst nm as e => e
  | eCase nm_i ty2 e bs =>
    let (nm, tys) := nm_i in
    eCase (nm, map (lift_type_vars n 0) tys)
          (lift_type_vars n 0 ty2) (reindexify n e)
          (map (fun p => (fst p, reindexify (length (fst p).(pVars) + n) (snd p))) bs)
  | eFix nm vn ty1 ty2 b =>
    eFix nm vn (lift_type_vars n 0 ty1) (lift_type_vars n 0 ty2) (reindexify (2+n) b)
  | eTy ty => eTy (lift_type_vars n 0 ty)
  end.

Fixpoint decompose_inductive (ty : type) : option (ename * list type) :=
  match ty with
  | tyInd x => Some (x,[])
  | tyForall nm ty => None
  | tyApp ty1 ty2 =>
      match decompose_inductive ty1 with
      | Some res =>let '(ind, tys) := res in Some (ind, (tys++[ty2])%list)
      | _ => None
      end
  | tyVar x => None
  | tyRel x => None
  | tyArr x x0 => None
  end.

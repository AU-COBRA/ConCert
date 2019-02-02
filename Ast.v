Require Template.All.

Require Import Template.Ast Template.AstUtils.
Require Import Template.Typing.
Require Import String List.

Import ListNotations.
Open Scope string_scope.

(* Aliases *)
Definition name := string.
Definition inductive := string.


Inductive type : Set :=
| tyInd : inductive -> type
| tyArr : type -> type -> type.

Record pat := pConstr {pName : name; pVars : list name}.

(** Type of language expressions. Corresponds to "core" Oak AST *)

(* NOTE: we have both named variables and de Bruijn indices.
   Translation to Template Coq requires indices, while named representation
   is what we get from real Oak programs.
   We can define relations on type of expressions ensuring that either
   names are used, or indices, but not both at the same time.

   Type annotations are required for the translation to Template Coq.
 *)
Inductive expr : Set :=
| eRel       : nat -> expr (*de Bruijn index *)
| eVar       : name -> expr (* named variables *)
| eLambda    : name -> type -> expr -> expr
| eLetIn     : name -> expr -> type -> expr -> expr
| eApp       : expr -> expr -> expr
| eConstr    : inductive -> name -> expr
| eConst     : name -> expr
| eCase      : (inductive * nat) (* # of parameters *) ->
               type ->
               expr (* discriminee *) ->
               list (pat * expr) (* branches *) ->
               expr
| eFix       : name (* of the fix *) -> name (* of the arg *) ->
               type (* of the arg *) -> type (* return type *) -> expr (* body *) -> expr.

(* An induction principle that takes into account nested occurrences of expressions
   in the list of branches for [eCase] *)
Definition expr_ind_case (P : expr -> Prop)
           (Hrel    : forall n : nat, P (eRel n))
           (Hvar    : forall n : name, P (eVar n))
           (Hlam    :forall (n : name) (t : type) (e : expr), P e -> P (eLambda n t e))
           (Hletin  : forall (n : name) (e : expr),
               P e -> forall (t : type) (e0 : expr), P e0 -> P (eLetIn n e t e0))
           (Happ    :forall e : expr, P e -> forall e0 : expr, P e0 -> P (eApp e e0))
           (Hconstr :forall (i : inductive) (n : name), P (eConstr i n))
           (Hconst  :forall n : name, P (eConst n))
           (Hcase   : forall (p : inductive * nat) (t : type) (e : expr),
               P e -> forall l : list (pat * expr), Forall (fun x => P (snd x)) l ->P (eCase p t e l))
           (Hfix    :forall (n n0 : name) (t t0 : type) (e : expr), P e -> P (eFix n n0 t t0 e)) :
  forall e : expr, P e.
Proof.
  refine (fix ind (e : expr) := _ ).
  destruct e.
  + apply Hrel.
  + apply Hvar.
  + apply Hlam. apply ind.
  + apply Hletin; apply ind.
  + apply Happ;apply ind.
  + apply Hconstr.
  + apply Hconst.
  + apply Hcase. apply ind.
    induction l.
    * constructor.
    * constructor. apply ind. apply IHl.
  + apply Hfix. apply ind.
Defined.

Definition vars_to_apps acc vs :=
  fold_left eApp vs acc.

Definition constr := (name * list type)%type.

(* Could be extended to handle declaration of constant, e.g. function definitions *)
Inductive global_dec :=
| gdInd : name -> list constr -> global_dec.

Definition global_env := list global_dec.

(* Associates names of types and constants of our language to the corresponding names in Coq *)
Definition translation_table := list (name * name).


Fixpoint lookup {A} (l : list (string * A)) key : option A :=
  match l with
  | [] => None
  | (key', v) :: xs => if eq_string key' key then Some v else lookup xs key
  end.

Fixpoint lookup_global ( Σ : global_env) key : option global_dec :=
  match Σ with
  | [] => None
  | gdInd key' v :: xs => if eq_string key' key then Some (gdInd key' v) else lookup_global xs key
  end.

Definition find_i {A : Type} (f : A -> bool) (l : list A) :=
let fix find (i : nat) (l : list A) : option (nat * A) :=
  match l with
  | [] => None
  | x :: tl => if f x then Some (i,x) else find (1+i) tl
  end in
find 0 l.

(* Resolves the constructor name to a corresponding position in the list of constructors along
   with the constructor info *)
Definition resolve_constr (Σ : global_env) (ind_name constr_name : ident)
  : option (nat * (string * list type)) :=
  match (lookup_global Σ ind_name) with
  | Some (gdInd n cs) => find_i (fun x => fst x =? constr_name) cs
  | None => None
  end.

Definition from_option {A : Type} ( o : option A) (default : A) :=
  match o with
  | None => default
  | Some v => v
  end.

Definition bump_indices (l : list (name * nat)) (n : nat) :=
  map (fun '(x,y) => (x, n+y)) l.

(* For a list of vars returns a list of pairs (var,number)
where the number is a position of the var counted from the end of the list.
 E.g. number_vars ["x"; "y"; "z"] = [("x", 2); ("y", 1); ("z", 0)] *)
Definition number_vars (ns : list name) : list (name * nat) :=
  combine ns (rev (seq 0 (length ns))).

Example number_vars_xyz : number_vars ["x"; "y"; "z"] = [("x", 2); ("y", 1); ("z", 0)].
Proof. reflexivity. Qed.

Fixpoint indexify (l : list (name * nat)) (e : expr) : expr :=
  match e with
  | eRel i => eRel i
  | eVar nm =>
    match (lookup l nm) with
    | None => (* FIXME: a hack to make the function total *)
      eVar ("not a closed term")
    | Some v => eRel v
    end
  | eLambda nm ty b =>
    eLambda nm ty (indexify ((nm,0 ):: bump_indices l 1) b)
  | eLetIn nm e1 ty e2 =>
    eLetIn nm e1 ty (indexify ((nm, 0) :: bump_indices l 1) e2)
  | eApp e1 e2 => eApp (indexify l e1) (indexify l e2)
  | eConstr t i as e => e
  | eConst nm as e => e
  | eCase nm_i ty e bs =>
    eCase nm_i ty (indexify l e)
          (map (fun p => (fst p, indexify (number_vars (fst p).(pVars) ++ bump_indices l (length (fst p).(pVars))) (snd p))) bs)
  | eFix nm vn ty1 ty2 b =>
    (* name of the fixpoint becomes an index as well *)
    eFix nm vn ty1 ty2 (indexify ((nm,1) :: (vn,0) :: bump_indices l 2) b)
  end.

Fixpoint type_to_term (ty : type) : term :=
  match ty with
  | tyInd i => tInd (mkInd i 0) []
  | tyArr t1 t2 => tProd nAnon (type_to_term t1) (type_to_term t2)
  end.


Fixpoint pat_to_lam (tys : list (name * type)) (body : term) : term :=
  match tys with
    [] => body
  | (n,ty) :: tys' => tLambda (nNamed n) (type_to_term ty) (pat_to_lam tys' body)
  end.

(* Resolves a pattern by looking up in the global environment
   and returns a list of pairs mapping pattern variable
   names to the types of the constructor arguments *)
Definition resolve_pat_arity (Σ : global_env) (ind_name : name) (p : pat) :=
  (* FIXME: in lookup failed we return a dummy value [(0,("",[]))]
     to make the function total *)
  combine p.(pVars)
  (snd (snd (from_option (resolve_constr Σ ind_name p.(pName)) (0,("",[]))))).

Definition expr_to_term (Σ : global_env) : expr -> Ast.term :=
  fix expr_to_term e :=
  match e with
  | eRel i => tRel i
  | eVar nm => tVar nm
  | eLambda nm ty b => tLambda (nNamed nm) (type_to_term ty) (expr_to_term b)
  | eLetIn nm e1 ty e2 => tLetIn (nNamed nm) (expr_to_term e1) (type_to_term ty) (expr_to_term e2)
  | eApp e1 e2 => tApp (expr_to_term e1) [expr_to_term e2]
  | eConstr t i => match (resolve_constr Σ t i) with
                     | Some c => tConstruct (mkInd t 0) (fst c) []
                     (* FIXME: a hack to make the function total *)
                     | None => tVar ("No declaration found: " ++ t)
                     end
  | eConst nm => tConst nm []
  | eCase nm_i ty e bs =>
    (* this interpretation is not complete, no translation for polymorphic types.
       Patterns must be in the same order as constructors in the definition *)
    let (nm,i) := nm_i in
    let typeInfo := tLambda nAnon (tInd (mkInd nm 0) []) (type_to_term ty) in
    let tys n := resolve_pat_arity Σ nm (fst n) in
    let branches :=
        List.map (fun x => (length (fst x).(pVars), pat_to_lam (tys x) (expr_to_term (snd x)))) bs in
    tCase (mkInd nm 0, i) typeInfo (expr_to_term e) branches
  | eFix nm nv ty1 ty2 b =>
    let tty1 := type_to_term ty1 in
    let tty2 := (type_to_term ty2) in
    let ty := tProd nAnon tty1 tty2 in
    let body := tLambda (nNamed nv) tty1 (expr_to_term b) in
    tFix [(mkdef _ (nNamed nm) ty body 0)] 0
  end.

Module BaseTypes.
  Definition Nat_name := "Coq.Init.Datatypes.nat".
  Definition Nat := tyInd Nat_name.
  Definition Bool_name := "Coq.Init.Datatypes.bool".
  Definition Bool := tyInd Bool_name.
  (* Definition true := eConstr Bool_name 0. *)
  (* Definition false := eConstr Bool_name 1. *)
End BaseTypes.

Import BaseTypes.

Declare Custom Entry expr.
Declare Custom Entry pat.
Declare Custom Entry type.

Notation "[| e |]" := e (e custom expr at level 2).
Notation "^ i " := (eRel i) (in custom expr at level 3, i constr at level 4).
Notation "x" := (eVar x) (in custom expr at level 0, x constr at level 4).
Notation "\ x : ty -> b" := (eLambda x ty b)
                              (in custom expr at level 1,
                                  ty constr at level 4,
                                  x constr at level 4).
Notation "'let' x : ty := e1 'in' e2" := (eLetIn x e1 ty e2)
                                           (in custom expr at level 1,
                                               ty constr at level 4,
                                               x constr at level 4).

(* Notation "C x .. y" := (pConstr C (cons x .. (cons y nil) .. )) *)
(*                          (in custom pat at level 1, *)
(*                              x constr at level 4, *)
(*                              y constr at level 4). *)

(* Could not make recursive notation work, so below there are several variants
   of [case] for different number of cases *)

(* Notation "'case' x : ty 'of'  b1 | .. | bn " := *)
(*   (eCase (ty,0) (tyInd "") x (cons b1 .. (cons bn nil) ..)) *)
(*     (in custom expr at level 1, *)
(*         b1 custom expr at level 4, *)
(*         bn custom expr at level 4, *)
(*         ty constr at level 4). *)


Notation "'case' x : ty1 'return' ty2 'of' | p1 -> b1 | pn -> bn" :=
  (eCase (ty1,0) ty2 x [(p1,b1);(pn,bn)])
    (in custom expr at level 1,
        p1 custom pat at level 4,
        pn custom pat at level 4,
        b1 custom expr at level 4,
        bn custom expr at level 4,
        ty1 constr at level 4,
        ty2 constr at level 4).

Notation "'case' x : ty1 'return' ty2 'of' p1 -> b1 " :=
  (eCase (ty1,0) ty2 x [(p1,b1)])
    (in custom expr at level 1,
        p1 custom pat at level 4,
        b1 custom expr at level 4,
        ty1 constr at level 4,
        ty2 constr at level 4).


Notation "t1 t2" := (eApp t1 t2) (in custom expr at level 4, left associativity).

Notation "'fix' fixname ( v : ty1 ) : ty2 := b" := (eFix fixname v ty1 ty2 b)
                                  (in custom expr at level 2,
                                      fixname constr at level 4,
                                      v constr at level 4,
                                      b custom expr at level 4,
                                      ty1 constr at level 4,
                                      ty2 constr at level 4).
Notation "( x )" := x (in custom expr, x at level 2).
Notation "{ x }" := x (in custom expr, x constr).

Module StdLib.
  Notation "a + b" := [| {eConst "Coq.Init.Nat.add"} {a} {b} |]
                        (in custom expr at level 0).
  Notation "a * b" := [| {eConst "Coq.Init.Nat.mul"} {a} {b} |]
                        (in custom expr at level 0).
  Notation "'Z'" := (eConstr Nat_name "Z") ( in custom expr at level 0).
  Notation "'Suc'" := (eConstr Nat_name "Suc") ( in custom expr at level 0).
  Notation "0" := [| Z |] ( in custom expr at level 0).
  Notation "1" := [| Suc Z |] ( in custom expr at level 0).

  Notation "'Z'" := (pConstr "Z" [])
                  (in custom pat at level 0).

  Notation "'Suc' x" := (pConstr "Suc" [x])
                    (in custom pat at level 0,
                        x constr at level 4).

  Notation "'true'" := (pConstr "true" []) (in custom pat at level 0).
  Notation "'false'" := (pConstr "false" []) ( in custom pat at level 0).

  Notation "'true'" := (eConstr Bool_name "true") (in custom expr at level 0).
  Notation "'false'" := (eConstr Bool_name "false") ( in custom expr at level 0).

  Definition Σ : global_env :=
    [gdInd Bool_name [("true", []); ("false", [])];
     gdInd Nat_name  [("Z", []); ("Suc", [tyInd Nat_name])]].
End StdLib.


Section Examples.
  Import StdLib.


  Definition x := "x".
  Definition y := "y".
  Definition z := "z".

  Check [| ^0 |].

  Check [| \x : Nat -> y |].

  Definition id_f_syn :=  [| (\x : Nat -> ^0) 1 |].

  Make Definition id_f_one := Eval compute in (expr_to_term Σ id_f_syn).
  Example id_f_eq : id_f_one = 1. Proof. reflexivity. Qed.

  (* The same as [id_f_syn], but with named vars *)
  Definition id_f_with_vars := [| (\x : Nat -> x) 1 |].

  Make Definition id_f_one' := Eval compute in (expr_to_term Σ (indexify [] id_f_with_vars)).
  Example id_f_eq' : id_f_one' = 1. Proof. reflexivity. Qed.

  Definition simple_let_syn :=
    [|
     \x : Nat ->
       let y : Nat := 1 in ^0
     |].

  Make Definition simple_let := Eval compute in (expr_to_term Σ simple_let_syn).
  Example simple_let_eq : simple_let 1 = 1. Proof. reflexivity. Qed.

  Definition simple_let_with_vars_syn :=
    [|
     \x : Nat ->
       let y : Nat := 1 in y
     |].

  Make Definition simple_let' := Eval compute in (expr_to_term Σ (indexify [] simple_let_with_vars_syn)).
  Example simple_let_eq' : simple_let' 0 = 1. Proof. reflexivity. Qed.


  Definition negb_syn :=
    [|
     \x : Bool ->
            case x : Bool_name return Bool of
            | true -> false
            | false -> true
    |].

  Make Definition negb' := Eval compute in (expr_to_term Σ (indexify [] negb_syn)).

  Example negb'_correct : forall b, negb' b = negb b.
  Proof.
    destruct b;easy.
  Qed.

  Definition myplus_syn :=
    [| \x : Nat -> \y : Nat -> x + y |].

  Make Definition myplus := Eval compute in (expr_to_term Σ (indexify [] myplus_syn)).

End Examples.

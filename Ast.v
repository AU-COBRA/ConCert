Require Template.All.

Require Import Bool.
Require Import Template.Ast Template.AstUtils.
Require Import Template.Typing.
Require Import String List.

Require Import MyEnv.

Import ListNotations.
Open Scope string_scope.

(* TODO: we use definition of monads from Template Coq,
   but (as actually comment in the [monad_utils] says, we
   should use a real monad library) *)
Require Import Template.monad_utils.
Import MonadNotation.

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

Fixpoint iclosed_n (n : nat) (e : expr) : bool :=
  match e with
  | eRel i => Nat.ltb i n
  | eVar x => false
  | eLambda nm ty b => iclosed_n (1+n) b
  | eLetIn nm e1 ty e2 => iclosed_n n e1 && iclosed_n (1+n) e2
  | eApp e1 e2 => iclosed_n n e1 && iclosed_n n e2
  | eConstr x x0 => true
  | eConst x => true
  | eCase ii ty e bs =>
    let bs'' := List.forallb
                  (fun x => iclosed_n (length ((fst x).(pVars)) + n) (snd x)) bs in
    iclosed_n n e && bs''
  | eFix fixname nm ty1 ty2 e => iclosed_n (2+n) e
  end.

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

Definition resolve_inductive (Σ : global_env) (ind_name : ident)
  : option (list (name * list type)) :=
  match (lookup_global Σ ind_name) with
  | Some (gdInd n cs) => Some cs
  | None => None
  end.

(* Resolves the constructor name to a corresponding position in the list of constructors along
   with the constructor info *)
Definition resolve_constr (Σ : global_env) (ind_name constr_name : ident)
  : option (nat * list type)  :=
  match (resolve_inductive Σ ind_name) with
  | Some cs => lookup_with_ind cs constr_name
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

Fixpoint pat_to_elam (tys : list (name * type)) (body : expr) : expr :=
  match tys with
    [] => body
  | (n,ty) :: tys' => eLambda n ty (pat_to_elam tys' body)
  end.


(* Resolves a pattern by looking up in the global environment
   and returns an index of the consrutor in the list of contrutors for the given iductive and
   a list of pairs mapping pattern variable names to the types of the constructor arguments *)
Definition resolve_pat_arity (Σ : global_env) (ind_name : name) (p : pat) : nat * list (name * type) :=
  (* NOTE: in lookup failed we return a dummy value [(0,("",[]))]
     to make the function total *)
  let o_ci := resolve_constr Σ ind_name p.(pName) in
  let (i, nm_tys) := from_option o_ci (0,[]) in
  (i, combine p.(pVars) nm_tys).

Definition trans_branch (bs : list (pat * term))
           (c : name * list type) :=
  let dummy := (pConstr "" [], tVar "error") in
  let (nm, tys) := c in
  let pt_e := from_option
                (find (fun '(p,e) =>p.(pName) =? nm) bs) dummy in
  let '(pt,e) := if (Nat.eqb #|(fst pt_e).(pVars)| #|tys|) then pt_e else dummy in
  let vars_tys := combine pt.(pVars) tys in
  (length pt.(pVars), pat_to_lam vars_tys e).

Definition fun_prod {A B C D} (f : A -> C) (g : B -> D) : A * B -> C * D := fun '(a,b) => (f a, g b).

Definition expr_to_term (Σ : global_env) : expr -> Ast.term :=
  fix expr_to_term e :=
  match e with
  | eRel i => tRel i
  | eVar nm => tVar nm
  | eLambda nm ty b => tLambda (nNamed nm) (type_to_term ty) (expr_to_term b)
  | eLetIn nm e1 ty e2 => tLetIn (nNamed nm) (expr_to_term e1) (type_to_term ty) (expr_to_term e2)
  | eApp e1 e2 => mkApps (expr_to_term e1) [expr_to_term e2]
  | eConstr t i => match (resolve_constr Σ t i) with
                     | Some c => tConstruct (mkInd t 0) (fst c) []
                     | None => tVar ("No declaration found: " ++ t)
                     end
  | eConst nm => tConst nm []
  | eCase nm_i ty e bs =>
    let (nm,i) := nm_i in
    let typeInfo := tLambda nAnon (tInd (mkInd nm 0) []) (type_to_term ty) in
    let cs := from_option (resolve_inductive Σ nm) [] in
    let tbs := map (fun_prod id expr_to_term) bs in
    let branches := map (trans_branch tbs) cs in
    (* TODO: no translation for polymorphic types, number of parameters is zero *)
    tCase (mkInd nm 0, 0) typeInfo (expr_to_term e) branches
  | eFix nm nv ty1 ty2 b =>
    let tty1 := type_to_term ty1 in
    let tty2 := type_to_term ty2 in
    let ty := tProd nAnon tty1 tty2 in
    let body := tLambda (nNamed nv) tty1 (expr_to_term b) in
    tFix [(mkdef _ (nNamed nm) ty body 0)] 0
  end.

Module BaseTypes.
  Definition Nat_name := "Coq.Init.Datatypes.nat".
  Definition Nat := Nat_name.

  Definition Bool_name := "Coq.Init.Datatypes.bool".
  Definition Bool := Bool_name.
End BaseTypes.

Import BaseTypes.

Declare Custom Entry expr.
Declare Custom Entry pat.
Declare Custom Entry type.

Notation "ty" := (tyInd ty) (in custom type at level 2, ty constr at level 3).
Notation "ty1 -> ty2" := (tyArr ty1 ty2)
                          (in custom type at level 4).

Notation "[| e |]" := e (e custom expr at level 2).
Notation "^ i " := (eRel i) (in custom expr at level 3, i constr at level 4).
Notation "x" := (eVar x) (in custom expr at level 0, x constr at level 4).
Notation "\ x : ty -> b" := (eLambda x ty b)
                              (in custom expr at level 1,
                                  ty custom type at level 2,
                                  b custom expr at level 4,
                                  x constr at level 4).
Notation "'let' x : ty := e1 'in' e2" := (eLetIn x e1 ty e2)
                                           (in custom expr at level 1,
                                               ty custom type at level 2,
                                               x constr at level 4).

(* Notation "C x .. y" := (pConstr C (cons x .. (cons y nil) .. )) *)
(*                          (in custom pat at level 1, *)
(*                              x constr at level 4, *)
(*                              y constr at level 4). *)

(* Could not make recursive notation work, so below, there are several variants
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
        ty2 custom type at level 4).

Notation "'case' x : ty1 'return' ty2 'of' p1 -> b1 " :=
  (eCase (ty1,0) ty2 x [(p1,b1)])
    (in custom expr at level 1,
        p1 custom pat at level 4,
        b1 custom expr at level 4,
        ty1 constr at level 4,
        ty2 custom type at level 4).


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
  Notation "a + b" := [| {eConst "Coq.Init.Nat.add"} {a} {b} |]
                        (in custom expr at level 0).
  Notation "a * b" := [| {eConst "Coq.Init.Nat.mul"} {a} {b} |]
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

  Definition true_name := "true".
  Definition false_name := "false".
  Notation "'true'" := (pConstr true_name []) (in custom pat at level 0).
  Notation "'false'" := (pConstr false_name []) ( in custom pat at level 0).

  Notation "'true'" := (eConstr Bool true_name) (in custom expr at level 0).
  Notation "'false'" := (eConstr Bool false_name) ( in custom expr at level 0).

  Definition Σ : global_env :=
    [gdInd Bool [("true", []); ("false", [])];
     gdInd Nat  [("Z", []); ("Suc", [tyInd Nat])]].
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
            case x : Bool return Bool of
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


Module Psubst.
  Definition psubst {A} := nat -> A.

  Definition id_subst : psubst := fun i => eRel i.
  Definition subst_cons {A} (e : A) (σ : psubst) : psubst :=
    fun i => if Nat.eqb i 0 then e else σ (i-1).

  Notation ids := id_subst.
  Notation "↑" := plus.
  Notation "e ⋅ σ" := (subst_cons e σ) (at level 50).

  Import Basics.
  Open Scope program_scope.

  Fixpoint erename (r : nat -> nat) (e : expr) : expr :=
    match e with
    | eRel i => eRel (r i)
    | eVar nm  => eVar nm
    | eLambda nm ty b => eLambda nm ty (erename (↑1 ∘ r) b)
    | eLetIn nm e1 ty e2 => eLetIn nm (erename r e1) ty (erename r e2)
    | eApp e1 e2 => eApp (erename r e1) (erename r e2)
    | eConstr t i as e' => e'
    | eConst nm => eConst nm
    | eCase nm_i ty e bs =>
      eCase nm_i ty (erename r e)
            (map (fun x =>
                    let k := length (fst x).(pVars) in
                    (fst x, erename (↑k ∘ r) (snd x))) bs)
    | eFix nm v ty1 ty2 b => eFix nm v ty1 ty2 (erename (↑2 ∘ r) b)
    end.

  Definition up (σ : psubst) := ids 0 ⋅ (erename (↑1) ∘ σ).

  Fixpoint up_k (k : nat) (σ : psubst) :=
    match k with
    | O => σ
    | S k' => up (up_k k' σ)
    end.

  Import FunctionalExtensionality.
  Import Lia.

  Lemma up_k_eq_id k σ :
    forall i,
    i < k ->
    up_k k σ i = ids i.
  Proof.
    induction k;intros i H.
    + inversion H.
    + simpl.
      destruct i. reflexivity.
      unfold up,subst_cons,compose. simpl.
      replace (i-0) with i by lia.
      rewrite IHk by lia. reflexivity.
  Qed.

  Reserved Notation "e .[ σ ]" (at level 0).

  Fixpoint apply_subst (σ : psubst) (e : expr) : expr :=
    match e with
    | eRel i => σ i
    | eVar nm  => eVar nm
    | eLambda nm ty b => eLambda nm ty (b .[up σ])
    | eLetIn nm e1 ty e2 => eLetIn nm (e1 .[σ]) ty (e2 .[up σ])
    | eApp e1 e2 => eApp (e1 .[σ]) (e2 .[σ])
    | eConstr t i as e' => e'
    | eConst nm => eConst nm
    | eCase nm_i ty e bs =>
      eCase nm_i ty (e .[σ])
            (map (fun x => (fst x, (snd x) .[up_k (length (fst x).(pVars)) σ])) bs)
    | eFix nm v ty1 ty2 b => eFix nm v ty1 ty2 (b .[up_k 2 σ])
  end
  where "e .[ σ ]" := (apply_subst σ e).

  Fixpoint lsubst (l : list expr) : psubst :=
    match l with
    | [] => ids
    | e :: l' => e ⋅ (lsubst l')
    end.

End Psubst.
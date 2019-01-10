Require Template.All.

Require Import Template.Ast.
Require Import Template.Typing.
Require Import String List.

Import ListNotations.

Open Scope string_scope.

Definition name := string.
Definition inductive := string.

Definition rName (nm : string) : Ast.aname := mkBindAnn (nNamed nm) Relevant.
Definition rAnon : Ast.aname := mkBindAnn nAnon Relevant.

Inductive type : Set :=
| tyInd : inductive -> type
| tyArr : type -> type -> type.

Fixpoint stupid_fix (n : nat) : nat :=
  match n with
  | O => 0
  | S n => stupid_fix n
  end.

Definition stupid_case (b : bool) : nat :=
  match b with
  | true => 1
  | false => 0
  end.

SearchPattern (bool -> bool).

Definition is_zero (n : nat) :=
  match n with
  | S n => false
  | O => true
  end.

Quote Recursively Definition q_stupid_fix := stupid_fix.
Definition Σ := (fst q_stupid_fix).
(* Eval compute in type_of_constructor Σ ((mkInd "Coq.Init.Datatypes.nat" 0),1) [] [] *)
Quote Definition q_stupid_case := Eval compute in stupid_case.
Quote Definition q_is_zero := Eval compute in is_zero.
Make Definition is_zero' := Eval compute in q_is_zero.
Quote Definition q_plus := Eval compute in plus.
Quote Definition q_app := Eval compute in app.

Definition ex_let n := let q := 1 in q + n.
Quote Definition q_let := (fun n => let q := 1 in q + n).

Inductive pat :=
| pConstr : name -> list name -> pat.

Inductive expr : Set :=
| eRel       : nat -> expr
| eVar       : name -> expr
| eLambda    : name -> type -> expr -> expr
| eLetIn     : name -> expr -> type -> expr -> expr
| eApp       : expr -> expr -> expr
| eConstruct : inductive -> nat -> expr
| eConst     : name -> expr
| eCase      : (inductive * nat) (* # of parameters *) -> type
               -> expr (* discriminee *) -> list (pat * expr) (* branches *) -> expr
(* | eProj      : projection -> expr -> expr *)
| eFix       : name -> type -> expr -> expr.
(* | eCoFix     : mfixpoint expr -> nat -> expr. *)

(* eq_string *)

Fixpoint lookup {A} (l : list (string * A)) key : option A :=
  match l with
  | [] => None
  | (key', v) :: xs => if eq_string key' key then Some v else lookup xs key
  end.

Definition from_option {A : Type} ( o : option A) (default : A) :=
  match o with
  | None => default
  | Some v => v
  end.

Fixpoint indexify (l : list (name * nat)) (e : expr) : expr :=
  match e with
  | eRel i => eRel i
  | eVar nm =>
    match (lookup l nm) with
    | None => eVar ("not a closed term") (* a hack to make the function total *)
    | Some v => eRel v
    end
  | eLambda nm ty b =>
    let bump_list := map (fun '(x,y) => (x, 1+y)) l in
    eLambda nm ty (indexify ((nm,0 ):: bump_list) b)
  | eLetIn nm e1 ty e2 =>
    let bump_list := map (fun '(x,y) => (x, 1+y)) l in
    eLetIn nm e1 ty (indexify ((nm, 0) :: bump_list) e2)
  | eApp e1 e2 => eApp (indexify l e1) (indexify l e2)
  | eConstruct t i as e => e
  | eConst nm as e => e
  | eCase nm_i ty e bs =>
    (* bracnhes are not handled properly yet; this only works for pattrens not binding any vars *)
    eCase nm_i ty (indexify l e) bs
  | eFix nm ty b =>
    let bump_list := map (fun '(x,y) => (x, 1+y)) l in
    eFix nm ty (indexify ((nm, 0) :: bump_list) b)
  end.

Fixpoint type_to_term (ty : type) : term :=
  match ty with
  | tyInd i => tInd (mkInd i 0) []
  | tyArr t1 t2 => tProd rAnon (type_to_term t1) (type_to_term t2)
  end.

SearchPattern (list _ -> list _ -> list _).

Definition numbered {A : Type} (l : list A) := combine (seq 0 (length l)) l.

Fixpoint expr_to_term (e : expr) : Ast.term :=
  match e with
  | eRel i => tRel i
  | eVar nm => tVar nm
  | eLambda nm ty b => tLambda (mkBindAnn (nNamed nm) Relevant) (type_to_term ty) (expr_to_term b)
  | eLetIn nm e1 ty e2 => tLetIn (rName nm) (expr_to_term e1) (type_to_term ty) (expr_to_term e2)
  | eApp e1 e2 => tApp (expr_to_term e1) [expr_to_term e2]
  | eConstruct t i => tConstruct (mkInd t 0) i []
  | eConst nm => tConst nm []
  | eCase nm_i ty e bs =>
    (* this interpretation is not complete, it ignores patterns and
       only works for constructors without parameters. Also, patterns must be in the same
     order as constructors in the definition *)
    let (nm,i) := nm_i in
    let typeInfo := tLambda rAnon (tInd (mkInd nm 0) []) (type_to_term ty) in
    tCase (mkInd nm 0, i) typeInfo None (expr_to_term e)
          (List.map (fun x => (0, expr_to_term (snd x))) bs)
  | eFix nm ty b => tFix [(mkdef _ (rName nm) (type_to_term ty) (expr_to_term b) 0)] 0
  end.

Module BaseTypes.
  Definition Nat_name := "Coq.Init.Datatypes.nat".
  Definition Nat := tyInd Nat_name.
  Definition Z := eConstruct Nat_name 0.
  Definition Suc := eConstruct Nat_name 1.

  Definition Bool_name := "Coq.Init.Datatypes.bool".
  Definition Bool := tyInd Bool_name.
  (* Definition true := eConstruct Bool_name 0. *)
  (* Definition false := eConstruct Bool_name 1. *)
End BaseTypes.

Import BaseTypes.

Declare Custom Entry expr.
Declare Custom Entry pat.

Notation "[| e |]" := e (e custom expr at level 2).
Notation "x" := (eVar x) (in custom expr at level 0, x constr at level 4).
Notation "^ i " := (eRel i) (in custom expr at level 3, i constr at level 4).
Notation "\ x : ty -> b" := (eLambda x ty b)
                              (in custom expr at level 1,
                                  ty constr at level 4,
                                  x constr at level 4).
Notation "'let' x : ty := e1 'in' e2" := (eLetIn x e1 ty e2)
                                           (in custom expr at level 1,
                                               ty constr at level 4,
                                               x constr at level 4).


(* Could not make recursive notation work, so below there are several variants
   of [case] for different number of cases *)

(* Notation "'case' x : ty 'of'  b1 | .. | bn " := *)
(*   (eCase (ty,0) (tyInd "") x (cons b1 .. (cons bn nil) ..)) *)
(*     (in custom expr at level 1, *)
(*         b1 custom expr at level 4, *)
(*         bn custom expr at level 4, *)
(*         ty constr at level 4). *)

Notation "'case' x : ty 'of' p1 -> b1 " :=
  (eCase (ty,0) (tyInd "") x [(p1,b1)])
    (in custom expr at level 1,
        b1 custom expr at level 4,
        ty constr at level 4).

Notation "'case' x : ty1 'return' ty2 'of' | p1 -> b1 | pn -> bn" :=
  (eCase (ty1,0) ty2 x [(p1,b1);(pn,bn)])
    (in custom expr at level 1,
        p1 custom pat at level 4,
        pn custom pat at level 4,
        b1 custom expr at level 4,
        bn custom expr at level 4,
        ty1 constr at level 4,
        ty2 constr at level 4).

Notation "'case' x : ty 'of' b1 | b2 | bn" :=
  (eCase (ty,0) (tyInd "") x [b1;b2;bn])
    (in custom expr at level 1,
        b1 custom expr at level 4,
        b2 custom expr at level 4,
        bn custom expr at level 4,
        ty constr at level 4).

Notation "'case' x : ty 'of' b1 | b2 | b3 | bn" :=
  (eCase (ty,0) (tyInd "") x [b1;b2;b3;bn])
    (in custom expr at level 1,
        b1 custom expr at level 4,
        b2 custom expr at level 4,
        b3 custom expr at level 4,
        bn custom expr at level 4,
        ty constr at level 4).

Notation "t1 t2" := (eApp t1 t2) (in custom expr at level 4, left associativity).
Notation "( x )" := x (in custom expr, x at level 2).
Notation "{ x }" := x (in custom expr, x constr).

Module StdLib.

  Notation "a + b" := [| {eConst "Coq.Init.Nat.add"} {a} {b} |]
                        (in custom expr at level 0).
  (* Notation "x" := x (in custom expr at level 0, x ident). *)
  Notation "0" := [| {Z} |] ( in custom expr at level 0).
  Notation "1" := [| {Suc} {Z} |] ( in custom expr at level 0).
  Notation "'true'" := (pConstr "true" []) (in custom pat at level 0).
  Notation "'false'" := (pConstr "false" []) ( in custom pat at level 0).

  Notation "'true'" := (eConstruct Bool_name 0) (in custom expr at level 0).
  Notation "'false'" := (eConstruct Bool_name 1) ( in custom expr at level 0).
End StdLib.

Import StdLib.


Definition x := "x".
Definition y := "y".
Definition z := "z".

Check [| ^0 |].

Check [| \x : Nat -> y |].

Definition id_f_syn :=  [| (\x : Nat -> ^0) 1 |].
Make Definition id_f_one := Eval compute in (expr_to_term id_f_syn).
Example id_f_eq : id_f_one = 1. Proof. reflexivity. Qed.

(* The same as [id_f_syn], but with named vars *)
Definition id_f_with_vars := [| (\x : Nat -> x) 1 |].

Make Definition id_f_one' := Eval compute in (expr_to_term (indexify [] id_f_with_vars)).
Example id_f_eq' : id_f_one' = 1. Proof. reflexivity. Qed.

Definition simple_let_syn :=
  [|
   \x : Nat ->
     let y : Nat := 1 in ^0
   |].

Make Definition simple_let := Eval compute in (expr_to_term simple_let_syn).
Example simple_let_eq : simple_let 1 = 1. Proof. reflexivity. Qed.

Definition simple_let_with_vars_syn :=
  [|
   \x : Nat ->
     let y : Nat := 1 in y
   |].

Make Definition simple_let' := Eval compute in (expr_to_term (indexify [] simple_let_with_vars_syn)).
Example simple_let_eq' : simple_let' 0 = 1. Proof. reflexivity. Qed.


Definition negb_syn :=
  [|
   \x : Bool ->
          case x : Bool_name return Bool of
          | true -> false
          | false -> true
  |].

Make Definition negb' := Eval compute in (expr_to_term (indexify [] negb_syn)).

Example negb'_correct : forall b, negb' b = negb b.
Proof.
  destruct b;easy.
Qed.

Definition myplus_syn :=
  [| \x : Nat -> \y : Nat -> x + y |].

Make Definition myplus := Eval compute in (expr_to_term (indexify [] myplus_syn)).

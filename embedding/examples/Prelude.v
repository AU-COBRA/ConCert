(** * Prelude -- definitions of basic of data types*)

(** Definitions of basic of data types required for the crowdfunding contract along with notations for developing contract using the deep embedding *)

Require Import String ZArith Basics.
From ConCert.Embedding Require Import Ast CustomTactics Notations
     PCUICTranslate PCUICtoTemplate.
Require Import List.

From MetaCoq.Template Require Import All.

Import MonadNotation.

Import ListNotations.
Import BaseTypes.
Open Scope list.


Definition expr_to_tc Σ := compose trans (expr_to_term Σ).
Definition type_to_tc := compose trans type_to_term.
Definition global_to_tc := compose trans_minductive_entry trans_global_dec.

(** Our approximation for finite maps. Eventually, will be replaced with the Oak's standard library implementation. We assume that the standard library is available for a contract developer. *)
Section Maps.
  Open Scope nat.

  Definition addr_map_acorn :=
    [\ data "addr_map" =
          "mnil" [_]
        | "mcons" [Nat, "Z", "addr_map",_] \].

  Make Inductive (global_to_tc addr_map_acorn).

  Fixpoint lookup_map (m : addr_map) (key : nat) : option Z :=
    match m with
    | mnil => None
    | mcons k v m' =>
      if (Nat.eqb key k) then Some v else lookup_map m' key
    end.

  (* Ported from FMapWeaklist of StdLib *)
  Fixpoint add_map (k : nat) (x : Z) (s : addr_map) : addr_map :=
  match s with
   | mnil => mcons k x mnil
   | mcons k' y l => if Nat.eqb k k' then mcons k x l else mcons k' y (add_map k x l)
  end.

  Definition inmap_map k m := match lookup_map m k with
                              | Some _ => true
                              | None => false
                              end.

  Lemma lookup_map_add k v m : lookup_map (add_map k v m) k = Some v.
  Proof.
    induction m.
    + simpl. now rewrite PeanoNat.Nat.eqb_refl.
    + simpl. destruct (k =? n) eqn:Heq.
      * simpl. now rewrite PeanoNat.Nat.eqb_refl.
      * simpl. now rewrite Heq.
  Qed.

  Fixpoint to_list (m : addr_map) : list (nat * Z)%type:=
    match m with
    | mnil => nil
    | mcons k v tl => cons (k,v) (to_list tl)
    end.

  Fixpoint of_list (l : list (nat * Z)) : addr_map :=
    match l with
    | nil => mnil
    | cons (k,v) tl => mcons k v (of_list tl)
    end.

  Lemma of_list_to_list m: of_list (to_list m) = m.
  Proof. induction m;simpl;congruence. Qed.

  Lemma to_list_of_list l: to_list (of_list l) = l.
  Proof. induction l as [ | x l'];simpl;auto.
         destruct x. simpl;congruence. Qed.

  Fixpoint map_forallb (p : Z -> bool)(m : addr_map) : bool:=
    match m with
    | mnil => true
    | mcons k v m' => p v && map_forallb p m'
    end.

  Lemma map_forallb_lookup_map p m k v :
    map_forallb p m = true ->
    lookup_map m k = Some v ->
    p v = true.
  Proof.
    revert k v p.
    induction m;intros;tryfalse;simpl in *.
    inv_andb H. destruct (_ =? _);auto.
    * now inversion H0;subst.
    * easy.
  Qed.

End Maps.

Notation "a ∈ m" := (inmap_map a m = true) (at level 50).
Notation "a ∉ m" := (inmap_map a m = false) (at level 50).

(** Notations for functions on finite maps *)

Definition Map := "addr_map".

Notation "'MNil'" := [| {eConstr "addr_map" "mnil"} |]
                       (in custom expr at level 0).

Notation "'mfind' a b" :=  [| {eConst "lookup_map"} {a} {b} |]
        (in custom expr at level 0,
            a custom expr at level 1,
            b custom expr at level 1).

Notation "'madd' a b c" :=  [| {eConst "add_map"} {a} {b} {c} |]
        (in custom expr at level 0,
            a custom expr at level 1,
            b custom expr at level 1,
            c custom expr at level 1).

Notation "'mem' a b" :=  [| {eConst "inmap_map"} {a} {b} |]
        (in custom expr at level 0,
            a custom expr at level 1,
            b custom expr at level 1).


  Definition Σ : list global_dec :=
  [gdInd Unit 0 [("tt", [])] false;
     gdInd Bool 0 [("true", []); ("false", [])] false;
     gdInd Nat 0 [("Z", []); ("Suc", [(None,tyInd Nat)])] false;
     gdInd "list" 1 [("nil", []); ("cons", [(None,tyRel 0);
                                              (None,tyApp (tyInd "list") (tyRel 0))])] false;
     gdInd "prod" 2 [("pair", [(None,tyRel 1);(None,tyRel 0)])] false].

Notation "a + b" := [| {eConst "Coq.ZArith.BinInt.Z.add"} {a} {b} |]
                      (in custom expr at level 0).
Notation "a * b" := [| {eConst "Coq.ZArith.BinInt.Z.mul"} {a} {b} |]
                      (in custom expr at level 0).
Notation "a - b" := [| {eConst "Coq.ZArith.BinInt.Z.sub"} {a} {b} |]
                      (in custom expr at level 0).
Notation "a == b" := [| {eConst "PeanoNat.Nat.eqb"} {a} {b} |]
                        (in custom expr at level 0).
Notation "a < b" := [| {eConst "Coq.ZArith.BinInt.Z.ltb"} {a} {b} |]
                      (in custom expr at level 0).
Notation "a <= b" := [| {eConst "Coq.ZArith.BinInt.Z.leb"} {a} {b} |]
                       (in custom expr at level 0).
Notation "a <n b" := [| {eConst "PeanoNat.Nat.ltb"} {a} {b} |]
                      (in custom expr at level 0).
Notation "a <=n b" := [| {eConst "PeanoNat.Nat.leb"} {a} {b} |]
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

Notation "A × B" := (tyApp (tyApp (tyInd "prod") A) B)
                        (in custom type at level 6,
                            A custom type,
                            B custom type at level 8).


Notation "'Pair' b o" :=
    (pConstr "pair" [b;o]) (in custom pat at level 0,
                                b constr at level 4,
                                o constr at level 4).

Notation "'Pair' A B b o" :=
    [| {eConstr "prod" "pair"} {eTy A} {eTy B} {b} {o} |]
      (in custom expr at level 0,
          A custom type at level 1,
          B custom type at level 1,
          b custom expr at level 1,
          o custom expr at level 1).

Notation "'first' A B p" := [| {eConst "fst"} {eTy A} {eTy B} {p} |]
                              (in custom expr at level 0,
                                  A custom type at level 1,
                                  B custom type at level 1,
                                  p custom expr at level 1).

Notation "'second' A B p" := [| {eConst "snd"} {eTy A} {eTy B} {p} |]
                              (in custom expr at level 0,
                                  A custom type at level 1,
                                  B custom type at level 1,
                                  p custom expr at level 1).

Definition Just := "Some".
Definition Nothing := "None".

Definition AcornList : global_dec :=
  gdInd "list" 1 [("nil", []);("cons", [(None, tyRel 0);(None, (tyApp (tyInd "list") (tyRel 0)))])] false.

Notation List := "list".

Notation "'Nil' A" :=
  [| {eConstr List "nil"} {eTy A}|]
    (in custom expr at level 0,
        A custom type at level 1).

Notation "'Cons' A x xs" :=
  [| {eConstr List "cons"} {eTy A} {x} {xs}|]
    (in custom expr at level 0,
        A custom type at level 1,
        x custom expr at level 1,
        xs custom expr at level 1).


Definition Maybe := "option".

Definition AcornMaybe : global_dec :=
  gdInd "option" 1 [("Some", [(None, tyRel 0)]);("None", [])] false.

Definition AcornProd : global_dec :=
  gdInd "prod" 2 [("pair", [(None, tyRel 1); (None, tyRel 0)])] false.


(** A shortcut for [if .. then .. else ..]  *)
Notation "'if' cond 'then' b1 'else' b2 : ty" :=
  (eCase (Bool,[]) ty cond
         [(pConstr true_name [],b1);(pConstr false_name [],b2)])
    (in custom expr at level 4,
        cond custom expr at level 4,
        ty custom type at level 4,
        b1 custom expr at level 4,
        b2 custom expr at level 4).

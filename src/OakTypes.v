From Coq Require Import ZArith.
From Containers Require Import Sets Maps.

Inductive OakType :=
  | oak_empty : OakType
  | oak_unit : OakType
  | oak_int : OakType
  | oak_bool : OakType
  | oak_sum : OakType -> OakType -> OakType
  | oak_pair : OakType -> OakType -> OakType
  | oak_list : OakType -> OakType
  | oak_set : OakType -> OakType
  | oak_map : OakType -> OakType -> OakType.

Lemma eq_oak_type_dec
  : forall (t1 t2 : OakType), {t1 = t2} + {t1 <> t2}.
Proof.
  decide equality.
Defined.

Program Instance Empty_set_StrictOrder
  : OrderedType.StrictOrder (fun (_ _ : Empty_set) => False) (@eq Empty_set).
Solve Obligations with contradiction.
Program Instance Empty_set_OrderedType : UsualOrderedType Empty_set.
Solve Obligations with contradiction.

(* These functions help some old Coq versions with inference *)
Definition make_sum (A B : Type) (_ : OrderedType A) (_ : OrderedType B)
  := existT OrderedType (A + B)%type _.

Definition make_pair (A B : Type) (_ : OrderedType A) (_ : OrderedType B)
  := existT OrderedType (A * B)%type _.

Definition make_list (A : Type) (_ : OrderedType A)
  := existT OrderedType (list A) _.

Definition make_set (A : Type) (_ : OrderedType A)
  := existT OrderedType (set A) _.

Definition make_map (A B : Type) (_ : OrderedType A) (_ : OrderedType B)
  := existT OrderedType Map[A, B] _.
  
Fixpoint interp_with_ordering (t : OakType) : {T : Type & OrderedType T} :=
  match t with
  | oak_empty => existT OrderedType Empty_set _
  | oak_unit => existT OrderedType unit _
  | oak_int => existT OrderedType Z _
  | oak_bool => existT OrderedType bool _
  | oak_sum a b =>
    let 'existT aT aOT := interp_with_ordering a in
    let 'existT bT bOT := interp_with_ordering b in
    make_sum aT bT aOT bOT
  | oak_pair a b =>
    let 'existT aT aOT := interp_with_ordering a in
    let 'existT bT bOT := interp_with_ordering b in
    make_pair aT bT aOT bOT
  | oak_list a =>
    let 'existT aT aOT := interp_with_ordering a in
    make_list aT aOT
  | oak_set a =>
    let 'existT aT aOT := interp_with_ordering a in
    make_set aT aOT
  | oak_map a b =>
    let 'existT aT aOT := interp_with_ordering a in
    let 'existT bT bOT := interp_with_ordering b in
    make_map aT bT aOT bOT
  end.

Definition interp (t : OakType) : Type :=
  projT1 (interp_with_ordering t).

Record OakValue :=
  build_oak_value {
    oak_value_type : OakType;
    oak_value : interp oak_value_type;
  }.

Definition oak_value_extract (t : OakType) (value : OakValue) : option (interp t).
Proof.
  destruct value as [ty val].
  destruct (eq_oak_type_dec t ty); subst.
  - apply (Some val).
  - apply None.
Defined.

(*
Examples:
Definition test_bool : OakValue := build_oak_value oak_bool true.
Definition test_int : OakValue := build_oak_value oak_int 5%Z.
Definition test_set : OakValue := build_oak_value (oak_set oak_int) {5%Z; {6%Z; {}}}.
Definition test_map : OakValue := build_oak_value (oak_map oak_int oak_int) [][5%Z <- 10%Z].

Compute (oak_value_extract oak_bool test_bool) : option bool.
Compute (oak_value_extract oak_int test_bool) : option Z.
Compute (oak_value_extract oak_bool test_int) : option bool.
Compute (oak_value_extract oak_int test_int) : option Z.
Compute (oak_value_extract (oak_set oak_int) test_set) : option (set Z).
Compute (option_map SetInterface.elements (oak_value_extract (oak_set oak_int) test_set)).
Compute (option_map elements (oak_value_extract (oak_map oak_int oak_int) test_map)).
*)
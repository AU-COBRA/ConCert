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

Definition eq_oak_type_dec (t1 t2 : OakType) : {t1 = t2} + {t1 <> t2}.
Proof. decide equality. Defined.

Program Instance empty_set_strict_order
  : OrderedType.StrictOrder (fun (_ _ : Empty_set) => False) (@eq Empty_set).
Solve Obligations with contradiction.
Program Instance empty_set_ordered_type : UsualOrderedType Empty_set.
Solve Obligations with contradiction.
  
Local Fixpoint interp_type_with_ordering (t : OakType) : {T : Type & OrderedType T} :=
  match t with
  | oak_empty => existT OrderedType Empty_set _
  | oak_unit => existT OrderedType unit _
  | oak_int => existT OrderedType Z _
  | oak_bool => existT OrderedType bool _
  | oak_sum a b =>
    let 'existT aT _ := interp_type_with_ordering a in
    let 'existT bT _ := interp_type_with_ordering b in
    existT OrderedType (aT + bT)%type _
  | oak_pair a b =>
    let 'existT aT _ := interp_type_with_ordering a in
    let 'existT bT _ := interp_type_with_ordering b in
    existT OrderedType (aT * bT)%type _
  | oak_list a =>
    let 'existT aT _ := interp_type_with_ordering a in
    existT OrderedType (list aT) _
  | oak_set a =>
    let 'existT aT _ := interp_type_with_ordering a in
    existT OrderedType (set aT) _
  | oak_map a b =>
    let 'existT aT _ := interp_type_with_ordering a in
    let 'existT bT _ := interp_type_with_ordering b in
    existT OrderedType Map[aT, bT] _
  end.

Definition interp_type (t : OakType) : Type :=
  projT1 (interp_type_with_ordering t).

Record OakValue :=
  build_oak_value {
    oak_value_type : OakType;
    oak_value : interp_type oak_value_type;
  }.

Definition oak_value_extract (t : OakType) (value : OakValue) : option (interp_type t).
Proof.
  destruct value as [ty val].
  destruct (eq_oak_type_dec t ty).
  - subst. exact (Some val).
  - exact None.
Defined.

(*
Examples:
Definition test_bool : OakValue := build_oak_value oak_bool true.
Definition test_int : OakValue := build_oak_value oak_int 5%Z.
Definition test_set : OakValue :=
  build_oak_value
    (oak_set oak_int)
    {5; {6; {}}}%Z.
Definition test_map : OakValue :=
  build_oak_value
    (oak_map oak_int oak_int)
    [][5 <- 10][6 <- 10][5 <- 15]%Z.

Definition test_map2 : OakValue :=
  build_oak_value
    (oak_map (oak_map oak_int oak_int) oak_int)
    [][[][5 <- 10][6 <- 10][5 <- 15] <- 15]%Z.

Compute (oak_value_extract oak_bool test_bool) : option bool.
Compute (oak_value_extract oak_int test_bool) : option Z.
Compute (oak_value_extract oak_bool test_int) : option bool.
Compute (oak_value_extract oak_int test_int) : option Z.
Compute (oak_value_extract (oak_set oak_int) test_set) : option (set Z).
Compute
  (oak_value_extract
     (oak_map
        (oak_map oak_int oak_int)
        oak_int)
     test_map2)
  : option Map[Map[Z, Z], Z].
Compute (option_map SetInterface.elements (oak_value_extract (oak_set oak_int) test_set)).
Compute (option_map elements (oak_value_extract (oak_map oak_int oak_int) test_map)).
*)
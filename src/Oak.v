From Coq Require Import ZArith.
From Containers Require Import Sets Maps.
From Containers Require SetProperties.
From SmartContracts Require Import Monads.
From Coq Require Import List.
From Coq Require Import Setoid.

Inductive OakType :=
  | oak_empty : OakType
  | oak_unit : OakType
  | oak_int : OakType
  | oak_bool : OakType
  | oak_pair : OakType -> OakType -> OakType
  | oak_sum : OakType -> OakType -> OakType
  | oak_list : OakType -> OakType
  | oak_set : OakType -> OakType
  | oak_map : OakType -> OakType -> OakType.

Definition eq_oak_type_dec (t1 t2 : OakType) : {t1 = t2} + {t1 <> t2}.
Proof. decide equality. Defined.

Proposition eq_oak_type_dec_refl (x : OakType) :
  eq_oak_type_dec x x = left eq_refl.
Proof.
  induction x;
    try simpl; try rewrite IHx; try rewrite IHx1; try rewrite IHx2; reflexivity.
Qed.

Program Instance empty_set_strict_order
  : OrderedType.StrictOrder (fun (_ _ : Empty_set) => False) (@eq Empty_set).
Solve Obligations with contradiction.
Program Instance empty_set_ordered_type : UsualOrderedType Empty_set.
Solve Obligations with contradiction.

Set Primitive Projections.
Local Record OakInterpretation :=
  build_interpretation {
    oi_ty : Type;
    oi_order : OrderedType oi_ty;
  }.

Local Fixpoint interp_type_with_ordering (t : OakType) : OakInterpretation :=
  match t with
  | oak_empty => build_interpretation Empty_set _
  | oak_unit => build_interpretation unit _
  | oak_int => build_interpretation Z _
  | oak_bool => build_interpretation bool _
  | oak_sum a b =>
    let (aT, _) := interp_type_with_ordering a in
    let (bT, _) := interp_type_with_ordering b in
    build_interpretation (aT + bT)%type _
  | oak_pair a b =>
    let (aT, _) := interp_type_with_ordering a in
    let (bT, _) := interp_type_with_ordering b in
    build_interpretation (aT * bT)%type _
  | oak_list a =>
    let (aT, _) := interp_type_with_ordering a in
    build_interpretation (list aT) _
  | oak_set a =>
    let (aT, _) := interp_type_with_ordering a in
    build_interpretation (set aT) _
  | oak_map a b =>
    let (aT, _) := interp_type_with_ordering a in
    let (bT, _) := interp_type_with_ordering b in
    build_interpretation Map[aT, bT] _
  end.

Definition interp_type (t : OakType) : Type :=
  oi_ty (interp_type_with_ordering t).

Record OakValue :=
  build_oak_value {
    oak_value_type : OakType;
    oak_value : interp_type oak_value_type;
  }.

Definition extract_oak_value (t : OakType) (value : OakValue) : option (interp_type t).
Proof.
  destruct value as [ty val].
  destruct (eq_oak_type_dec t ty).
  - subst. exact (Some val).
  - exact None.
Defined.

(* Defines that a type can be serialized into OakValue and deserialized from it,
   and that these are inverses *)
Class OakTypeEquivalence (ty : Type) :=
  {
    serialize : ty -> OakValue;
    deserialize : OakValue -> option ty;
    ote_equivalence : forall (x : ty), deserialize (serialize x) = Some x;
  }.

Global Opaque serialize deserialize ote_equivalence.

Definition make_trivial_equiv (ot : OakType) : OakTypeEquivalence (interp_type ot).
Proof.
  refine {| serialize := build_oak_value ot;
            deserialize := extract_oak_value ot;
            ote_equivalence := _ |}.
  intros x.
  unfold extract_oak_value.
  rewrite eq_oak_type_dec_refl.
  reflexivity.
Defined.

Instance oak_empty_equivalence : OakTypeEquivalence Empty_set :=
  make_trivial_equiv oak_empty.

Instance oak_unit_equivalence : OakTypeEquivalence unit :=
  make_trivial_equiv oak_unit.

Instance oak_int_equivalence : OakTypeEquivalence Z :=
  make_trivial_equiv oak_int.

Instance oak_bool_equivalence : OakTypeEquivalence bool :=
  make_trivial_equiv oak_bool.

Program Instance oak_nat_equivalence : OakTypeEquivalence nat :=
  {| serialize n := serialize (Z.of_nat n);
     deserialize z := do z' <- deserialize z; Some (Z.to_nat z'); |}.
Next Obligation.
  rewrite ote_equivalence.
  simpl.
  rewrite Nat2Z.id.
  reflexivity.
Qed.

Program Instance oak_value_equivalence : OakTypeEquivalence OakValue :=
  {| serialize v := v;
     deserialize v := Some v; |}.

Generalizable Variables A B.
Program Instance oak_sum_equivalence
        `{e_a : OakTypeEquivalence A}
        `{e_b : OakTypeEquivalence B}
  : OakTypeEquivalence (A + B)%type :=
  {| serialize s :=
       let (is_left, ov) :=
           match s with
           | inl l => (true, serialize l)
           | inr r => (false, serialize r)
           end in
       build_oak_value (oak_pair oak_bool ov.(oak_value_type)) (is_left, ov.(oak_value));
     deserialize os :=
       match os with
       | build_oak_value (oak_pair oak_bool v) (b, val) =>
         if b
         then do a <- @deserialize _ e_a (build_oak_value v val);
              Some (inl a)
         else do b <- @deserialize _ e_b (build_oak_value v val);
              Some (inr b)
       | _ => None
       end;
  |}.
Next Obligation.
  destruct x as [a | b]; rewrite ote_equivalence; reflexivity.
  (*
  - change ({| oak_value_type := oak_value_type (serialize a);
               oak_value := oak_value (serialize a) |}) with (serialize a).

    rewrite ote_equivalence.
  *)
Qed.

Program Instance oak_pair_equivalence
        `{e_a : OakTypeEquivalence A}
        `{e_b : OakTypeEquivalence B}
  : OakTypeEquivalence (A * B)%type :=
  {| serialize '(a, b) :=
       let 'build_oak_value a_oty a_val := serialize a in
       let 'build_oak_value b_oty b_val := serialize b in
       build_oak_value (oak_pair a_oty b_oty) (a_val, b_val);
     deserialize op :=
       match op with
       | build_oak_value (oak_pair a_ty b_ty) (a_val, b_val) =>
         do a <- @deserialize _ e_a (build_oak_value a_ty a_val);
         do b <- @deserialize _ e_b (build_oak_value b_ty b_val);
         Some (a, b)
       | _ => None
       end;
  |}.
Next Obligation.
  repeat rewrite ote_equivalence.
  reflexivity.
Qed.

Program Instance oak_list_equivalence
        `{OakTypeEquivalence A}
  : OakTypeEquivalence (list A) :=
  {| serialize l :=
       let go a acc :=
           let 'build_oak_value a_oty a_val := serialize a in
           let 'build_oak_value acc_oty acc_val := acc in
           build_oak_value (oak_pair a_oty acc_oty) (a_val, acc_val) in
       fold_right go (build_oak_value oak_unit tt) l;
     deserialize ol :=
       let fix aux (ty : OakType) (val : interp_type ty) : option (list A) :=
           match ty with
           | oak_pair hd_ty tl_ty =>
             let pair : interp_type hd_ty * interp_type tl_ty := ltac:(subst; exact val) in
             let (hd_val, tl_val) := pair in
             do hd <- deserialize (build_oak_value hd_ty hd_val);
             do tl <- aux tl_ty tl_val;
             Some (hd :: tl)
           | oak_unit => Some nil
           | _ => None
           end in
       let 'build_oak_value ol_ty ol_val := ol in
       aux ol_ty ol_val;
  |}.
Solve Obligations with split; discriminate.
Next Obligation.
  induction x as [| hd tl IHl].
  - reflexivity.
  - simpl.
    rewrite IHl.
    rewrite ote_equivalence.
    reflexivity.
Qed.

Program Instance oak_map_equivalence
        `{OakTypeEquivalence A}
        `{OrderedType A}
        `{OakTypeEquivalence B}
  : OakTypeEquivalence Map[A, B] :=
  {| serialize m := serialize (MF.to_list m);
     deserialize om :=
       do elems <- deserialize om;
       Some (MF.of_list elems);
  |}.
Next Obligation.
  (* TODO: Need to use setoids here... *)
  Admitted.

Program Instance oak_set_equivalence
        `{OakTypeEquivalence A}
        `{OrderedType A}
  : OakTypeEquivalence (SetInterface.set A) :=
  {| serialize s := serialize (SetProperties.to_list s);
     deserialize os :=
       do elems <- deserialize os;
       Some (SetProperties.of_list elems);
  |}.
Next Obligation.
  (* TODO: Setoids ... *)
  Admitted.

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

Compute (extract_oak_value oak_bool test_bool) : option bool.
Compute (extract_oak_value oak_int test_bool) : option Z.
Compute (extract_oak_value oak_bool test_int) : option bool.
Compute (extract_oak_value oak_int test_int) : option Z.
Compute (extract_oak_value (oak_set oak_int) test_set) : option (set Z).
Compute
  (extract_oak_value
     (oak_map
        (oak_map oak_int oak_int)
        oak_int)
     test_map2)
  : option Map[Map[Z, Z], Z].
Compute (option_map SetInterface.elements (extract_oak_value (oak_set oak_int) test_set)).
Compute (option_map elements (extract_oak_value (oak_map oak_int oak_int) test_map)).
*)

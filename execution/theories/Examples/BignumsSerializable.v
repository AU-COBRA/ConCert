From Bignums Require Import BigN.
From Bignums Require Import BigZ.
From Coq Require Import ZArith.
From Coq Require Import DoubleType.
Require Import Monads.
Require Import Serializable.

Section IntSer.
  Definition int_serializable
             (T := BigN.dom_t 0)
             (to_Z : T -> Z)
             (of_Z : Z -> T)
             (of_to_Z : forall t, of_Z (to_Z t) = t) : Serializable T.
  Proof.
    refine
      {| serialize t := serialize (to_Z t);
         deserialize p := do z <- deserialize p; ret (of_Z z); |}.
    intros x.
    rewrite deserialize_serialize.
    cbn.
    now rewrite of_to_Z.
  Defined.

  (* Massive hack: ltac inside notation is only checked at expansion time.
   This allows the proof below to work for Coq 8.10 where Bignums uses int63
   and Coq 8.9 where Bignums uses int31 and int63 does not even exist. *)
  Local Set Warnings "-non-reversible-notation".
  Notation "'lazyexp' x" := ltac:(exact x) (at level 70).

  Global Instance int_serializable_inst : Serializable (BigN.dom_t 0).
  Proof.
    first
      [exact
         (int_serializable
            (lazyexp Int31.phi)
            (lazyexp Int31.phi_inv)
            (lazyexp Cyclic31.phi_inv_phi))|
       exact
         (int_serializable
            (lazyexp Int63.to_Z)
            (lazyexp Int63.of_Z)
            (lazyexp Int63.of_to_Z))].
  Defined.
End IntSer.

Global Instance zn2z_serializable {A} `{Serializable A} : Serializable (zn2z A).
Proof.
  refine
    {| serialize w1 :=
         serialize
           match w1 with
           | W0 => (0%nat, serialize tt)
           | WW a b => (1%nat, serialize (a, b))
           end;
       deserialize p :=
         do '(tag, p) <- deserialize p;
         match tag with
         | 0%nat => ret W0
         | _ => do '(a, b) <- deserialize p;
                ret (WW a b)
         end |}.
  intros.
  rewrite deserialize_serialize.
  cbn.
  destruct x; auto.
  now rewrite deserialize_serialize.
Defined.
Global Instance word_serializable {A} `{Serializable A} (n : nat) : Serializable (word A n) :=
  (fix f (n : nat) :=
     match n return (Serializable (word A n)) with
     | 0%nat => _ : Serializable A
     | S n => zn2z_serializable
     end) n.

Global Instance BigNw1_serializable : Serializable BigN.w1 := ltac:(apply zn2z_serializable).
Global Instance BigNw2_serializable : Serializable BigN.w2 := ltac:(apply zn2z_serializable).
Global Instance BigNw3_serializable : Serializable BigN.w3 := ltac:(apply zn2z_serializable).
Global Instance BigNw4_serializable : Serializable BigN.w4 := ltac:(apply zn2z_serializable).
Global Instance BigNw5_serializable : Serializable BigN.w5 := ltac:(apply zn2z_serializable).
Global Instance BigNw6_serializable : Serializable BigN.w6 := ltac:(apply zn2z_serializable).
Global Instance BigN_serializable : Serializable bigN.
Proof.
  refine
    {| serialize n :=
         match n with
         | BigN.N0 i => serialize (0, serialize i)
         | BigN.N1 w => serialize (1, serialize w)
         | BigN.N2 w => serialize (2, serialize w)
         | BigN.N3 w => serialize (3, serialize w)
         | BigN.N4 w => serialize (4, serialize w)
         | BigN.N5 w => serialize (5, serialize w)
         | BigN.N6 w => serialize (6, serialize w)
         | BigN.Nn n w => serialize (7, serialize (n, serialize w))
         end%nat;
       deserialize p :=
         do '(tag, p) <- deserialize p;
         match tag with
         | 0 => option_map BigN.N0 (deserialize p)
         | 1 => option_map BigN.N1 (deserialize p)
         | 2 => option_map BigN.N2 (deserialize p)
         | 3 => option_map BigN.N3 (deserialize p)
         | 4 => option_map BigN.N4 (deserialize p)
         | 5 => option_map BigN.N5 (deserialize p)
         | 6 => option_map BigN.N6 (deserialize p)
         | 7 => do '(n, p) <- deserialize p;
                do w <- deserialize p;
                ret (BigN.Nn n w)
         | _ => None
         end%nat |}.
  intros [].
  all: rewrite ?deserialize_serialize; cbn.
  all: rewrite ?deserialize_serialize; easy.
Defined.
Global Instance BigZ_serializable : Serializable bigZ :=
  Derive Serializable BigZ.t__rect<BigZ.Pos, BigZ.Neg>.

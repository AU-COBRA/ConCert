(** * Evaluation environments *)

Require Import String List PeanoNat Coq.micromega.Lia.

From ConCert.Embedding Require Import CustomTactics.

Import ListNotations.

Definition env (A : Type) := list (string * A).

(** Lookup by variable name *)
Fixpoint lookup {A} (ρ : env A) (key : string) : option A :=
  match ρ with
  | [] => None
  | (nm,a) :: ρ' =>
    if (eqb nm key) then Some a else lookup ρ' key
  end.

Fixpoint lookup_with_ind_rec {A} (i : nat) (ρ : env A) (key : string) : option (nat * A) :=
  match ρ with
  | [] => None
  | (nm,a) :: ρ' =>
    if (eqb nm key) then Some (i,a)
    else lookup_with_ind_rec (1+i) ρ' key
  end.

Definition lookup_with_ind {A} (ρ : env A) (key : string)
  : option (nat * A) := lookup_with_ind_rec 0 ρ key.


  (** Lookup by index (similar to [List.nth_error], but defined by recursion on env *)
Fixpoint lookup_i {A} (ρ : env A) (i : nat) : option A :=
  match ρ with
  | [] => None
  | (nm,a) :: ρ' =>
    if (Nat.eqb i 0) then Some a else lookup_i ρ' (i-1)
  end.

  (** A value environment lookup: *)
Notation "ρ # '(' k ')'" := (lookup ρ k) (at level 10).
(** A value environment extension: *)
Notation "ρ # [ k ~> v ]" := ( (k,v) :: ρ) (at level 50).

Fixpoint remove_by_key {A} (key : string) (ρ : env A) : env A :=
  match ρ with
  | [] => []
  | (nm,a) :: ρ' => if (eqb nm key) then remove_by_key key ρ'
                  else (nm,a) :: (remove_by_key key ρ')
  end.

Lemma lookup_i_length {A} (ρ : env A) n :
  (n <? length ρ) = true -> {e | lookup_i ρ n = Some e}.
Proof.
  intros H. revert dependent n.
  induction ρ;intros;leb_ltb_to_prop;simpl in *.
  elimtype False. lia.
  destruct a. destruct n.
  + simpl;eauto.
  + simpl. assert (n < length ρ) by lia. replace (n-0) with n by lia.
    prop_to_leb_ltb. now apply IHρ.
Qed.

Lemma lookup_i_length_false {A} (ρ : env A) n :
  (n <? length ρ) = false -> lookup_i ρ n = None.
Proof.
  intros H. revert dependent n.
  induction ρ;intros;leb_ltb_to_prop;simpl in *;auto.
  destruct a. destruct n.
  + simpl;eauto. inversion H.
  + simpl. assert (length ρ <= n) by lia. replace (n-0) with n by lia.
    rewrite <- PeanoNat.Nat.ltb_ge in *.
    now apply IHρ.
Qed.

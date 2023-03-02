(** * Extensions for Prelude from Embedding *)

(** Extends Prelude from Embedding with new definitions required for extraction *)

From ConCert.Embedding Require Import Ast.
From ConCert.Embedding Require Import Notations.
From ConCert.Embedding Require Import PCUICTranslate.
From ConCert.Embedding Require Import TranslationUtils.
From ConCert.Embedding Require Import Prelude.
From ConCert.Embedding Require Import Utils.
From ConCert.Execution Require Import Blockchain.
From ConCert.Execution Require Import Serializable.
From ConCert.Utils Require Import Automation.
From Coq Require Import String.
From Coq Require Import ZArith.
From Coq Require Import List.

From MetaCoq.Template Require Import All.

Import MCMonadNotation.
Import ListNotations.
Import BaseTypes.
Open Scope list.
Open Scope nat.

(** ** Wrappers for some primitive types *)

MetaCoq Run
        ( mp_ <- tmCurrentModPath tt ;;
          let mp := (PCUICTranslate.string_of_modpath mp_ ++ "@")%string in
          mkNames mp ["address"; "time"; "ContractAddr";
                      "UserAddr"; "Time" ; "Money" ] "_coq").


Definition address_ty :=
  [\ data address =
      ContractAddr [Nat,_]
    | UserAddr [Nat, _] \].

MetaCoq Unquote Inductive (global_to_tc address_ty).

Definition time_ty :=
  [\ data time = Time [Nat,_] \].

MetaCoq Unquote Inductive (global_to_tc time_ty).

Definition money := to_string_name <% Z %>.


(** Comparison for addresses and time *)

Definition ltb_time (t1 t2 : time_coq) :=
  let '(Time_coq n1) := t1 in
    let '(Time_coq n2) := t2 in
    n1 <? n2.

Definition leb_time (t1 t2 : time_coq) :=
  let '(Time_coq n1) := t1 in
  let '(Time_coq n2) := t2 in
  n1 <=? n2.

Definition eqb_addr (a1 a2 : address_coq) :=
  match a1,a2 with
  | ContractAddr_coq n1, ContractAddr_coq n2 => Nat.eqb n1 n2
  | UserAddr_coq n1, UserAddr_coq n2 => Nat.eqb n1 n2
  | _, _ => false
  end.


(** Additional notations for addresses *)

 Notation "a ==a b" := [| {eConst (to_string_name <% eqb_addr %>)} {a} {b} |]
                        (in custom expr at level 0).


(** Additional notations for time *)

Notation "a <t b" := [| {eConst (to_string_name <% ltb_time %>)} {a} {b} |]
                      (in custom expr at level 0).
Notation "a <=t b" := [| {eConst (to_string_name <% leb_time %>)} {a} {b} |]
                       (in custom expr at level 0).

(** A simplified representation of a call context.
    Contains: current time, sender, transaction amount, contract's balance *)
Notation "'CallCtx'" := [! time × (address × (money × money)) !]
                         (in custom type at level 0).

Notation "'current_time' st" :=
  [| first time (address × (money × money)) {st} |]
    (in custom expr at level 0).

Notation "'sender_addr' st" :=
  [| first address (money × money) (second time (address × (money × money)) {st}) |]
    (in custom expr at level 0).

Notation "'sent_amount' st" :=
  [| first money money (second address (money × money) (second time (address × (money × money)) {st})) |]
    (in custom expr at level 0).

Notation "'acc_balance' st" :=
  [| second money money (second address (money × money) (second time (address × (money × money)) {st})) |]
    (in custom expr at level 0).

Notation "'mkCallCtx' now sender sent_am bal " :=
  [| Pair time (address × (money × money)) {now}
          (Pair address (money × money) {sender}
                (Pair money money {sent_am} {bal} )) |]
    (in custom expr at level 0).

(** A simple representation of the call context *)

(** current_time, sender_add, sent_amount, acc_balance *)
Definition SimpleCallCtx : Set := time_coq × (address_coq × (Amount × Amount)).

(** These projections correspond to the notations above *)
Definition sc_current_time (ctx : SimpleCallCtx) : time_coq := ctx.1.
Definition sc_sender_addr (ctx : SimpleCallCtx) : address_coq := ctx.2.1.
Definition sc_sent_amount (ctx : SimpleCallCtx) : Z := ctx.2.2.1.
Definition sc_acc_balance (ctx : SimpleCallCtx) : Z := ctx.2.2.2.


Definition is_contract (addr: address_coq) :=
  match addr with
  | ContractAddr_coq _ => true
  | UserAddr_coq _ => false
  end.

Definition encode_addr (addr: address_coq) : nat + nat :=
  match addr with
  | ContractAddr_coq x => inl x
  | UserAddr_coq x => inr x
  end.

Definition decode_addr (addr: nat + nat) : address_coq :=
  match addr with
  | inl x => ContractAddr_coq x
  | inr x => UserAddr_coq x
  end.


Global Program Instance CB : ChainBase :=
  build_chain_base address_coq eqb_addr _ _ _ _ is_contract.
Next Obligation.
  intros a b. destruct a,b; simpl.
  - destruct (n =? n0)%nat eqn:Heq.
    * constructor. now rewrite Nat.eqb_eq in *.
    * constructor. now rewrite NPeano.Nat.eqb_neq in *.
  - now constructor.
  - now constructor.
  - destruct (n =? n0)%nat eqn:Heq.
    * constructor. now rewrite Nat.eqb_eq in *.
    * constructor. now rewrite NPeano.Nat.eqb_neq in *.
Qed.
Next Obligation.
  intros ??. unfold base.Decision.
  decide equality; apply Nat.eq_dec.
Qed.
Next Obligation.
  assert (cnat : countable.Countable (nat + nat)) by typeclasses eauto.
  destruct cnat as [e d H].
  unshelve econstructor.
  * intros addr. destruct addr.
    exact (e (inl n)).
    exact (e (inr n)).
  * intros i.
    destruct (d i).
    ** destruct s as [n | n].
       exact (Some (ContractAddr_coq n)).
       exact (Some (UserAddr_coq n)).
    ** exact None.
  * cbn; intros addr.
    destruct addr;
    now rewrite H.
Defined.
Next Obligation.
  assert (snat : Serializable.Serializable (nat + nat)) by typeclasses eauto.
  destruct snat as [s d H].
  unshelve econstructor.
  * intros addr. destruct addr.
    exact (s (inl n)).
    exact (s (inr n)).
  * intros i.
    destruct (d i) as [v | ].
    ** destruct v as [n | n].
       exact (Some (ContractAddr_coq n)).
       exact (Some (UserAddr_coq n)).
    ** exact None.
  * cbn; intros addr.
    destruct addr;
      now rewrite H.
Defined.

Definition init_wrapper {setup storage}
           (init : SimpleCallCtx -> setup -> storage)
           (ch : Chain)
           (ctx : ContractCallContext) : setup -> storage :=
  let simple_ctx :=
      (Time_coq ch.(current_slot),
       ((ctx.(ctx_from)),
        ((ctx.(ctx_amount), ctx.(ctx_contract_balance))))) in
    init simple_ctx.


(** Our approximation for finite maps. We cannot use the one defined in the
    Embedding.Prelude, because it cannot be made parametric wrt. the type of
    keys doe to limitations of the embedding (types cannot be constants,
    only inductives) *)
Module Maps.
  Open Scope nat.


  MetaCoq Run
          ( mp_ <- tmCurrentModPath tt ;;
            let mp := (PCUICTranslate.string_of_modpath mp_ ++ "@")%string in
            mkNames mp ["addr_map" ] "_coq").

  Definition addr_map_acorn :=
    [\ data addr_map =
          "mnil" [_]
        | "mcons" [address, money, addr_map,_] \].

  MetaCoq Unquote Inductive (global_to_tc addr_map_acorn).

  Definition Map := to_string_name <% addr_map_coq %>.

  Fixpoint lookup_map (m : addr_map_coq) (key : address_coq) : option Z :=
    match m with
    | mnil => None
    | mcons k v m' =>
      if (eqb_addr key k) then Some v else lookup_map m' key
    end.

  (* Ported from FMapWeaklist of StdLib *)
  Fixpoint add_map (k : address_coq) (x : Z) (s : addr_map_coq) : addr_map_coq :=
  match s with
   | mnil => mcons k x mnil
   | mcons k' y l => if eqb_addr k k' then mcons k x l else mcons k' y (add_map k x l)
  end.

  Definition inmap_map k m := match lookup_map m k with
                              | Some _ => true
                              | None => false
                              end.

  Lemma lookup_map_add k v m : lookup_map (add_map k v m) k = Some v.
  Proof.
    induction m.
    + simpl. destruct k; simpl; now rewrite PeanoNat.Nat.eqb_refl.
    + simpl. destruct (eqb_addr k a) eqn:Heq.
      * destruct k; simpl; now rewrite PeanoNat.Nat.eqb_refl.
      * simpl. now rewrite Heq.
  Qed.

  Fixpoint to_list (m : addr_map_coq) : list (address_coq * Z)%type :=
    match m with
    | mnil => nil
    | mcons k v tl => cons (k,v) (to_list tl)
    end.

  Fixpoint of_list (l : list (address_coq * Z)) : addr_map_coq :=
    match l with
    | nil => mnil
    | cons (k,v) tl => mcons k v (of_list tl)
    end.

  Lemma of_list_to_list m: of_list (to_list m) = m.
  Proof. induction m; simpl; congruence. Qed.

  Lemma to_list_of_list l: to_list (of_list l) = l.
  Proof. induction l as [ | x l']; simpl; auto.
         destruct x. simpl; congruence. Qed.

  Fixpoint map_forallb (p : Z -> bool)(m : addr_map_coq) : bool :=
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
    induction m; intros; try discriminate; simpl in *.
    propify. destruct (eqb_addr _ _); auto.
    * now inversion H0; subst.
    * easy.
  Qed.


  (** Notations for functions on finite maps *)

  Notation "'MNil'" := [| {eConstr Map "mnil"} |]
                         (in custom expr at level 0).

  Notation "'mfind' a b" := [| {eConst (to_string_name <% lookup_map %>)} {a} {b} |]
          (in custom expr at level 0,
              a custom expr at level 1,
              b custom expr at level 1).

  Notation "'madd' a b c" := [| {eConst (to_string_name <% add_map %>)} {a} {b} {c} |]
          (in custom expr at level 0,
              a custom expr at level 1,
              b custom expr at level 1,
              c custom expr at level 1).

  Notation "'mem' a b" := [| {eConst (to_string_name <% inmap_map %>)} {a} {b} |]
          (in custom expr at level 0,
              a custom expr at level 1,
              b custom expr at level 1).

End Maps.

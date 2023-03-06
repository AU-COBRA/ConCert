From ConCert.Execution Require Import Monad.

Inductive result T E :=
| Ok (t : T)
| Err (e : E).

Arguments Ok {_ _}.
Arguments Err {_ _}.

Global Instance Monad_result {E} : Monad (fun T => result T E) :=
  {| ret _ t := Ok t;
     bind _ _ mt f :=
     match mt with
     | Ok t => f t
     | Err e => Err e
     end |}.

Global Instance MonadLaws_Monad_result {E} : MonadLaws (@Monad_result E).
Proof.
  constructor.
  - auto.
  - intros; cbn.
    destruct t; auto.
  - intros; cbn.
    destruct t; auto.
Qed.

Definition result_of_option {T E : Type} (o : option T) (err : E) : result T E :=
  match o with
  | Some a => Ok a
  | None => Err err
  end.

Definition option_of_result {T E : Type} (r : result T E) : option T :=
  match r with
  | Ok t => Some t
  | Err e => None
  end.

Global Instance option_to_result
        {E : Type}
        : MonadTrans (fun T => E -> result T E) option :=
  {| lift T (opt : option T) err := @result_of_option T E opt err |}.

Global Instance result_to_option
        {E : Type}
        : MonadTrans option (fun T => result T E) :=
  {| lift T (opt : result T E) := @option_of_result T E opt |}.

Definition unpack_result {T E : Type} (r : result T E) :=
  match r return match r with
                  | Ok _ => T
                  | Err _ => E
                  end with
  | Ok t => t
  | Err e => e
  end.

Definition bind_error {T E1 E2 : Type} (f : E1 -> E2) (r : result T E1) : result T E2 :=
  match r with
  | Ok t => Ok t
  | Err e => Err (f e)
  end.

Definition isOk {T E : Type} (r : result T E) :=
  match r with | Ok _ => true | Err _ => false end.
Definition isErr {T E : Type} (r : result T E) :=
  match r with | Ok _ => false | Err _ => true end.


Lemma result_of_option_eq_some : forall {T E : Type} (x : option T) (e : E) (y : T),
  result_of_option x e = Ok y <-> x = Some y.
Proof.
  split; destruct x; intros eq;
  (discriminate || injection eq as <-; reflexivity).
Qed.

Lemma result_of_option_eq_none : forall {T E : Type} (x : option T) (e1 e2 : E),
  result_of_option x e1 = Err e2 -> x = None.
Proof.
  destruct x;
  (discriminate || reflexivity).
Qed.

Lemma isOk_Ok : forall {T E : Type} (r : result T E) (x : T),
  r = Ok x -> isOk r = true.
Proof.
  intros.
  now subst.
Qed.

Lemma isOk_Err : forall {T E : Type} (r : result T E) (e : E),
  r = Err e -> isOk r = false.
Proof.
  intros.
  now subst.
Qed.

Lemma isOk_exists : forall {T E : Type} (r : result T E),
  isOk r = true <-> exists x : T, r = Ok x.
Proof.
  split.
  - intros.
    destruct r; eauto.
    discriminate.
  - intros (x & r_eq).
    eapply isOk_Ok.
    eauto.
Qed.

Lemma isOk_not_exists : forall {T E : Type} (r : result T E),
  isOk r = false <-> forall x : T, r <> Ok x.
Proof.
  split.
  - now destruct r.
  - intros r_eq.
    destruct r; auto.
    congruence.
Qed.

Lemma isOk_neq_isErr : forall {T E : Type} (r : result T E),
  isOk r <> isErr r.
Proof.
  intros.
  destruct r; cbn; congruence.
Qed.

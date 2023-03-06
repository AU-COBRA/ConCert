(** This file defines some helpful notations for monads. *)
From Coq Require Import List.
From Coq Require Import Basics.

Class Monad (m : Type -> Type) : Type :=
build_monad {
  ret : forall {t}, t -> m t;
  bind : forall {t u}, m t -> (t -> m u) -> m u
}.

Notation "c >>= f" := (bind c f) (at level 50, left associativity).
Notation "f =<< c" := (bind c f) (at level 51, right associativity).

Notation "'do' x <- c1 ; c2" :=
  (bind c1 (fun x => c2))
    (at level 60, c1 at next level, right associativity).

Notation "'do' ' pat <- c1 ; c2" :=
  (bind c1 (fun x => match x with pat => c2 end))
    (at level 60, pat pattern, c1 at next level, right associativity).

Notation "'do' e1 ; e2" := (do _ <- e1 ; e2)
  (at level 60, right associativity).

Class MonadLaws {m : Type -> Type} (mon : Monad m) :=
build_monad_laws {
  bind_of_return :
    forall (T : Type) (t : T) (U : Type) (f : T -> m U),
      (ret t >>= f) = f t;
  return_of_bind :
    forall (T : Type) (t : m T),
      (t >>= @ret m mon T) = t;
  bind_assoc :
    forall (T U V : Type) (t : m T) (f : T -> m U) (g : U -> m V),
      (t >>= f) >>= g = t >>= (fun t => f t >>= g);
}.

Class MonadTrans (m : Type -> Type) (mt : Type -> Type) : Type :=
  { lift : forall {t}, mt t -> m t }.

Fixpoint monad_map {A B} {m : Type -> Type}
                  `{Monad m} (f : A -> m B)
                   (xs : list A) : m (list B) :=
  match xs with
  | nil => ret nil
  | cons x xs' =>
      do v <- f x;
      do vs <- monad_map f xs';
      ret (cons v vs)
  end.

Lemma monad_map_map {A B Z} {m : Type -> Type} `{Monad m}
      (f : A -> m B) (g : Z -> A) (xs : list Z) :
  monad_map f (map g xs) = monad_map (compose f g) xs.
Proof.
  induction xs.
  - easy.
  - cbn. now rewrite IHxs.
Qed.

Fixpoint monad_foldr {A B} {m : Type -> Type}
                    `{Monad m} (f : A -> B -> m A)
                     (a : A) (xs : list B) : m A :=
  match xs with
  | nil => ret a
  | cons x xs' => do v <- monad_foldr f a xs';
                  f v x
  end.

Fixpoint monad_foldl {A B} {m : Type -> Type}
                    `{Monad m} (f : A -> B -> m A)
                     (a : A) (xs : list B) : m A :=
  match xs with
  | nil => ret a
  | cons x xs' => do v <- f a x;
                  monad_foldl f v xs'
  end.

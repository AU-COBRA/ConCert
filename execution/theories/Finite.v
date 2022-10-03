(* This file captures what it means for a type to be finite *)

From Coq Require Import List.
Import ListNotations.

Class Finite (T : Type) :=
  build_finite {
    elements : list T;
    elements_set : NoDup elements;
    elements_all : forall (t : T), In t elements;
  }.

Arguments elements _ {_}.
Arguments elements_set _ {_}.
Arguments elements_all _ {_}.

#[export]
Hint Resolve elements_set elements_all : core.

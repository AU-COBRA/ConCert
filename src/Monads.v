Definition option_bind {A B : Type} (v : option A) (f : A -> option B) : option B :=
  match v with
  | Some val => f val
  | None => None
  end.

Notation "c >>= f" := (option_bind c f) (at level 50, left associativity).
Notation "f =<< c" := (option_bind c f) (at level 51, right associativity).

Notation "'do' x <- c1 ; c2" :=
  (option_bind c1 (fun x => c2))
    (at level 60, c1 at next level, right associativity).

Notation "'do' ' pat <- c1 ; c2" :=
  (option_bind c1 (fun x => match x with pat => c2 end))
    (at level 60, pat pattern, c1 at next level, right associativity).

Notation "'do' e1 ; e2" := (do _ <- e1 ; e2)
  (at level 60, right associativity).

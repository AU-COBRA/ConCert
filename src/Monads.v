Definition option_bind {A B : Type} (f : A -> option B) (v : option A) : option B :=
  match v with
  | Some val => f val
  | None => None
  end.

Notation "'do' X <- A ; B" := (option_bind (fun X => B) A)
                                (at level 200, X ident, A at level 100, B at level 200).

Notation "'do' X : T <- A ; B" := (option_bind (fun x : T => B) A)
                                    (at level 200, X ident, A at level 100, B at level 200).
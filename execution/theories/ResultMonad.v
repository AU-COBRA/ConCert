From ConCert.Execution Require Import Monads.

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

Definition result_of_option {T E} (o : option T) (err : E) : result T E :=
  match o with
  | Some a => Ok a
  | None => Err err
  end.

Definition option_of_result {T E} (r : result T E) : option T :=
  match r with
  | Ok t => Some t
  | Err e => None
  end.

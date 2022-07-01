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

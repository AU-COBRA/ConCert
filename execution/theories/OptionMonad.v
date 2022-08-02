From ConCert.Execution Require Import Monad.

Global Instance Monad_option : Monad option :=
  {| ret _ t := Some t;
     bind _ _ v f := match v with
                 | Some val => f val
                 | None => None
                 end |}.

Global Instance MonadLaws_Monad_option : MonadLaws Monad_option.
Proof.
  constructor.
  - auto.
  - intros; cbn.
    destruct t; auto.
  - intros; cbn.
    destruct t; auto.
Qed.

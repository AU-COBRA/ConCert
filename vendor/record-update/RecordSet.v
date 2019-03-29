Set Implicit Arguments.

(** Reader is the reader monad (or just the function monad). We only use
Applicative here. *)
Definition Reader E T := forall (e:E), T e.
Arguments Reader : clear implicits.

(* pure/return *)
Definition constructor {E T} (x:T) : Reader E (fun _ => T) := fun _ => x.

(* Applicative's (<*>) (written as `ap`).

This has an awkwardly long name since it's intended to be used infix with
 *)
Definition applicative_ap {E}
           {A: E -> Type}
           {B: forall (e:E), A e -> Type}
           (f: Reader E (fun e => forall (a:A e), B e a)) :
  forall (x: Reader E A), Reader E (fun e => B e (x e))  :=
  fun x => fun e => f e (x e).

(** Settable is a way of accessing a constructor for a record of type T. The
syntactic form of this definition is important: it must be an eta-expanded
version of T's constructor, written generically over the field accessors of T.
The best way to do this for a record X := mkX { A; B; C} is
[settable! mkX <A; B; C>]. *)
Class Settable T := { mkT: Reader T (fun _ => T);
                      mkT_ok: forall x, mkT x = x }.
Arguments mkT T mk : clear implicits, rename.

Local Ltac solve_mkT_ok :=
  match goal with
  | |- forall x, _ = _ => solve [ destruct x; cbv; f_equal ]
  end.

(** settable! creates an instance of Settable from a constructor and list of
fields. *)
Notation "'settable!' mk < f1 ; .. ; fn >" :=
  (Build_Settable
     (applicative_ap .. (applicative_ap (constructor mk) f1) .. fn)
     ltac:(solve_mkT_ok)) (at level 0, mk at level 10, f1, fn at level 9, only parsing).

(** [setter] creates a setter based on an eta-expanded record constructor and a
particular field projection proj *)
Local Ltac setter etaT proj :=
  let set :=
      (match eval pattern proj in etaT with
       | ?setter ?proj => constr:(fun f => setter (fun r => f (proj r)))
       end) in
  let set := (eval cbv [constructor applicative_ap] in set) in
  exact set.

(* Combining the above, [getSetter'] looks up the eta-expanded version of T with
the Settable typeclass, and calls [setter] to create a setter. *)
Local Ltac get_setter T proj :=
  match constr:(mkT T _) with
  | mkT _ ?updateable =>
    let updateable := (eval hnf in updateable) in
    match updateable with
    | {| mkT := ?mk |} =>
      setter mk proj
    end
  end.

(* Setter provides a way to change a field given by a projection function, along
with correctness conditions that require the projected field and only the
projected field is modified. *)
Class Setter {R T} (proj: R -> T) := set : (T -> T) -> R -> R.
Arguments set {R T} proj {Setter}.

Class SetterWf {R T} (proj: R -> T) :=
  { set_wf :> Setter proj;
    set_get: forall v r, proj (set proj v r) = v (proj r);
    set_eq: forall r, set proj (fun x => x) r = r; }.

Arguments set_wf {R T} proj {SetterWf}.

Local Ltac SetterInstance_t :=
  match goal with
  | |- @Setter ?T _ ?A => get_setter T A
  end.

Local Ltac SetterWfInstance_t :=
  match goal with
  | |- @SetterWf ?T _ ?A =>
    unshelve notypeclasses refine (Build_SetterWf _ _ _);
    [ get_setter T A |
      let r := fresh in
      intros ? r; destruct r |
      let r := fresh in
      intros r; destruct r ];
    intros; reflexivity
  end.

Hint Extern 1 (Setter _) => SetterInstance_t : typeclass_instances.
Hint Extern 1 (SetterWf _) => SetterWfInstance_t : typeclass_instances.

Module RecordSetNotations.
  Delimit Scope record_set with rs.
  Open Scope rs.
  Notation "x <| proj  :=  v |>" := (set proj (constructor v) x)
                                    (at level 12, left associativity) : record_set.
  Notation "x <| proj  ::=  f |>" := (set proj f x)
                                     (at level 12, f at next level, left associativity) : record_set.
End RecordSetNotations.

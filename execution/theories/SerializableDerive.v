From ConCert.Execution Require Import Monad.
From ConCert.Execution Require Import OptionMonad.
From ConCert.Execution Require Import SerializableBase.



Ltac make_serializer_case ty :=
  match ty with
  | ?T1 -> ?T2 =>
    let rest := make_serializer_case T2 in
    constr:(fun (f : SerializedValue -> SerializedValue) (v : T1) =>
              rest (fun (cur : SerializedValue) => f (serialize (v, cur))))
  | SerializedValue =>
    constr:(fun (f : SerializedValue -> SerializedValue) => f (serialize tt))
  end.

Ltac make_serializer_aux term tag :=
  match type of term with
  | ?T1 -> (?T2 -> ?T3) =>
    let cs := make_serializer_case T1 in
    let cs := constr:(cs (fun x => serialize (tag, x))) in
    let term := (eval hnf in (term cs)) in
    make_serializer_aux term (S tag)
  | ?T -> SerializedValue =>
    term
  end.

Ltac make_serializer eliminator :=
  let term := (eval hnf in (eliminator (fun _ => SerializedValue))) in
  let serializer := make_serializer_aux term 0 in
  eval cbn in serializer.

Ltac make_deserializer_case ty :=
  match ty with
  | ?T1 -> ?T2 =>
    let rest := make_deserializer_case T2 in
    constr:(fun builder sv =>
              do '(a, sv) <- (deserialize sv : option (T1 * SerializedValue));
              rest (builder a) sv)
  | ?T => constr:(fun (value : T) (sv : SerializedValue) =>
              do _ <- (deserialize sv : option unit);
              Some value)
  end.

Ltac make_deserializer_aux ctors rty :=
  match ctors with
  | (?ctor, ?tl) =>
    let ty := type of ctor in
    let cs := make_deserializer_case ty in
    let rest := make_deserializer_aux tl rty in
    constr:(
      fun tag sv =>
        match tag with
        | 0 => cs ctor sv
        | S tag => rest tag sv
        end)
  | tt => constr:(fun (tag : nat) (sv : SerializedValue) => @None rty)
  end.

Ltac get_final_type ty :=
  match ty with
  | ?T1 -> ?T2 => get_final_type T2
  | ?T => T
  end.

Ltac make_deserializer ctors rty :=
  let deser := make_deserializer_aux ctors rty in
  let deser := constr:(fun sv => do '(tag, sv) <- deserialize sv; deser tag sv) in
  eval cbn in deser.

Ltac get_ty_from_elim_ty ty :=
  match ty with
  | forall (_ : ?T -> Type), _ => T
  end.

Ltac make_serializable eliminator ctors :=
  let ser := make_serializer eliminator in
  let elim_ty := type of eliminator in
  let ty := get_ty_from_elim_ty elim_ty in
  let deser := make_deserializer ctors ty in
  exact
    {| serialize := ser;
       deserialize := deser;
       deserialize_serialize :=
         ltac:(intros []; repeat (cbn in *; try rewrite deserialize_serialize; auto)) |}.

Notation "'Derive' 'Serializable' rect" :=
  ltac:(make_serializable rect tt) (at level 0, rect at level 10, only parsing).

Notation "'Derive' 'Serializable' rect < c0 , .. , cn >" :=
  (let pairs := pair c0 .. (pair cn tt) .. in
   ltac:(
     (* This matches last-to-first so it always finds 'pairs' *)
     match goal with
     | [pairs := ?x |- _] => make_serializable rect x
     end))
    (at level 0, rect at level 10, c0, cn at level 9, only parsing).

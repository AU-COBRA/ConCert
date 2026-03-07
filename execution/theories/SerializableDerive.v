From ConCert.Execution Require Import Monad.
From ConCert.Execution Require Import OptionMonad.
From ConCert.Execution Require Import SerializableBase.
From Ltac2 Require Ltac2.



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



Module DeriveSer.
  Import Ltac2.

  Ltac2 fail s :=
    Control.zero (Tactic_failure (Some (Message.of_string s))).

  Ltac2 assert_oib ind :=
    if Int.gt (Ind.nblocks ind) 1 then
      fail "Mututal inductives not supported"
    else
      ().

  Ltac2 apply_params c p :=
    Constr.Unsafe.make (Constr.Unsafe.App c p).

  Ltac2 get_constructors ind p :=
    let ncons := Ind.nconstructors ind in
    let cons_i := List.seq 0 1 ncons in
    List.fold_right (fun x acc =>
        let c := Env.instantiate (Std.ConstructRef (Ind.get_constructor ind x)) in
        let c := apply_params c p in
        '(($c, $acc))
        ) cons_i '(tt).

  Ltac2 get_rect ind :=
    let id := Env.path (Std.IndRef ind) in
    let id' := Ident.of_string (String.app (Ident.to_string (List.last id)) "_rect") in
    let id' := Option.map (fun x => List.append (List.removelast id) [x]) id' in
    let id' := Option.bind id' (fun x => Env.get x) in
    let id' := Option.map (fun x => Env.instantiate x) id' in
    match id' with
    | Some c => c
    | None => fail "Could not find _rect definition"
    end.

  Ltac2 get_ind x :=
    match (Constr.Unsafe.kind x) with
    | Constr.Unsafe.Ind ind _ => (Array.empty, ind)
    | Constr.Unsafe.App c l =>
      match (Constr.Unsafe.kind c) with
      | Constr.Unsafe.Ind ind _ => (l, ind)
      | _ => fail "Argument not an inductive type"
      end
    | _ => fail "Argument not an inductive type"
    end.

  Ltac2 assert_nparam_correct n p :=
    if Int.equal (Array.length p) n then
      ()
    else
      fail "Error: invalid parameters".

  Ltac2 derive_serializable x :=
    let (params, ind) := get_ind x in
    let i := Ind.data ind in
    assert_oib i;
    let n_params := Ind.nparams i in
    assert_nparam_correct n_params params;
    let cons_l := get_constructors i params in
    let c_rect := apply_params (get_rect ind) params in
    ltac1:(rect l |- make_serializable rect l) (Ltac1.of_constr c_rect) (Ltac1.of_constr cons_l).

  Ltac2 auto_derive_serializable () :=
    lazy_match! goal with
    | [ |- Serializable ?e ] => derive_serializable e
    | [ |- _] => fail "Goal is not an Serializable instance"
    end.

  Notation "'Derive' 'Ser'" :=
    ltac2:(auto_derive_serializable ()) (only parsing).

End DeriveSer.

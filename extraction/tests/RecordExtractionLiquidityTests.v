Local Unset Universe Checking.
From Coq Require Import List.
From Coq Require Import String.
From MetaCoq.Template Require Import All.
From ConCert.Extraction Require Import Common.
From ConCert.Utils Require Import StringExtra.
From ConCert.Extraction Require Import LiquidityExtract.

Import ListNotations.

Local Set Universe Checking.

Local Open Scope string_scope.

Definition PREFIX := "".
Definition TT_defs :=
  [
    remap <%% nat %%> "nat"
  ].

Definition unwrap_sum {A} (s : A + A) : A :=
  match s with
  | inl v | inr v => v
  end.


Module RecordsWithoutPrimitiveProjections.
  Record A := build_A {
    x : nat;
  }.

  Definition proj_A (a : A) : nat := a.(x).

  MetaCoq Quote Recursively Definition proj_A_quoted := proj_A.
  (* Print proj_A_quoted. *)

  Definition proj_A_printed :=
    Eval vm_compute in unwrap_sum (liquidity_extract_single TT_defs [] true "" "" proj_A_quoted).

  Example A_printed_as_type_alias :
    proj_A_printed =?
    <$ "";
    "";
    "type a = nat";
    "";
    "let proj_A (a : a) = a";
    "";
    "" $>.
  Proof. reflexivity. Qed.

  Definition constructA : A :=
    let a1 := {| x := 0 |} in
    let a2 := build_A 0 in
    a1.

  MetaCoq Quote Recursively Definition constructA_quoted := constructA.

  Definition constructA_printed :=
    Eval vm_compute in unwrap_sum (liquidity_extract_single TT_defs [] true "" "" constructA_quoted).

  Example constructA_omits_constructor :
    constructA_printed =?
    <$
    "";
    "";
    "type a = nat";
    "";
    "let constructA  = let a1 = O in ";
    "let a2 = O in ";
    "a1";
    "";
    "" $>.
  Proof. reflexivity. Qed.

  Record B := build_B {
    y : nat;
    z : nat;
  }.

  Definition proj_B (b : B) := b.(z).

  MetaCoq Quote Recursively Definition proj_B_quoted := proj_B.
  (* Print proj_B_quoted. *)

  Definition proj_B_printed :=
    Eval vm_compute in unwrap_sum (liquidity_extract_single TT_defs [] true "" "" proj_B_quoted).

  Example B_printed_as_type_alias :
    proj_B_printed =?
    <$"";
    "";
    "type b = {";
    "y : nat;";
    "z : nat";
    "}";
    "";
    "let proj_B (b : b) = b.z";
    "";
    "" $>.
  Proof. reflexivity. Qed.

  Definition constructB : B :=
    let B1 := {| y := 0; z := 0 |} in
    let B2 := build_B 0 0 in
    B1.

  MetaCoq Quote Recursively Definition constructB_quoted := constructB.

  Definition constructB_printed :=
    Eval vm_compute in unwrap_sum (liquidity_extract_single TT_defs [] true "" "" constructB_quoted).

  Example constructB_uses_record_syntax :
    constructB_printed =?
    <$"";
    "";
    "type b = {";
    "y : nat;";
    "z : nat";
    "}";
    "";
    "let constructB  = let b1 = {y = O; z = O} in ";
    "let b2 = {y = O; z = O} in ";
    "b1";
    "";
    "" $>.
  Proof. reflexivity. Qed.

End RecordsWithoutPrimitiveProjections.

Module RecordWithPrimitiveProjections.
(* Essentially, we expect the exact same results as when primitive projections are disabled *)
  Set Primitive Projections.
  Record A := build_A {
    x : nat;
  }.

  Definition proj_A (a : A) : nat := a.(x).

  MetaCoq Quote Recursively Definition proj_A_quoted := proj_A.
  (* Print proj_A_quoted. *)

  Definition proj_A_printed :=
    Eval vm_compute in unwrap_sum (liquidity_extract_single TT_defs [] true "" "" proj_A_quoted).

  Example A_printed_as_type_alias :
    proj_A_printed =?
    <$"";
    "";
    "type a = nat";
    "";
    "let proj_A (a : a) = a";
    "";
    "" $>.
  Proof. reflexivity. Qed.

  Definition constructA : A :=
    let a1 := {| x := 0 |} in
    let a2 := build_A 0 in
    a1.

  MetaCoq Quote Recursively Definition constructA_quoted := constructA.

  Definition constructA_printed :=
    Eval vm_compute in unwrap_sum (liquidity_extract_single TT_defs [] true "" "" constructA_quoted).

  Example constructA_omits_constructor :
    constructA_printed =?
    <$"";
    "";
    "type a = nat";
    "";
    "let constructA  = let a1 = O in ";
    "let a2 = O in ";
    "a1";
    "";
    "" $>.
  Proof. reflexivity. Qed.

  Record B := build_B {
    y : nat;
    z : nat;
  }.

  Definition proj_B (b : B) := b.(z).

  MetaCoq Quote Recursively Definition proj_B_quoted := proj_B.

  Definition proj_B_printed :=
    Eval vm_compute in unwrap_sum (liquidity_extract_single TT_defs [] true "" "" proj_B_quoted).

  Example B_printed_as_type_alias :
    proj_B_printed =?
    <$"";
    "";
    "type b = {";
    "y : nat;";
    "z : nat";
    "}";
    "";
    "let proj_B (b : b) = b.z";
    "";
    "" $>.
  Proof. reflexivity. Qed.


  Definition constructB : B :=
    let B1 := {| y := 0; z := 0 |} in
    let B2 := build_B 0 0 in
    B1.

  MetaCoq Quote Recursively Definition constructB_quoted := constructB.

  Definition constructB_printed :=
    Eval vm_compute in unwrap_sum (liquidity_extract_single TT_defs [] true "" "" constructB_quoted).

  Example constructB_uses_record_syntax :
    constructB_printed =?
    <$ "";
    "";
    "type b = {";
    "y : nat;";
    "z : nat";
    "}";
    "";
    "let constructB  = let b1 = {y = O; z = O} in ";
    "let b2 = {y = O; z = O} in ";
    "b1";
    "";
    "" $>.
  Proof. reflexivity. Qed.

End RecordWithPrimitiveProjections.

From ConCert.Extraction Require Import Common.
From ConCert.Extraction Require Import MidlangExtract.
From ConCert.Extraction Require Import Optimize.
From ConCert.Extraction Require Import PrettyPrinterMonad.
From ConCert.Extraction Require Import ResultMonad.
From Coq Require Import Arith.
From Coq Require Import String.
From MetaCoq.Template Require Import Ast.
From MetaCoq.Template Require Import Loader.
From MetaCoq Require Import monad_utils.
From MetaCoq Require Import utils.

Import MonadNotation.
Local Open Scope string.

Definition extract (p : program) : result string string :=
  entry <- match p.2 with
           | tConst kn _ => ret kn
           | _ => Err "Expected program to be a tConst"
           end;;
  Σ <- specialize_erase_debox_template_env p.1 [entry] [];;
  let Σ := remove_unused_args Σ in
  '(_, s) <- finish_print (print_env Σ p.1 (fun _ => None));;
  ret s.

Module ex1.
  Definition foo : { n : nat | n = 0 } := exist _ 0 eq_refl.
  Definition bar := proj1_sig foo.
  MetaCoq Quote Recursively Definition ex1 := bar.

  Definition ex1_expected :=
"type Sig a p" ++ nl ++
"  = Exist a" ++ nl ++
"" ++ nl ++
"proj1_sig : Sig a □ -> a" ++ nl ++
"proj1_sig e =" ++ nl ++
"  case e of" ++ nl ++
"    Exist a ->" ++ nl ++
"      a" ++ nl ++
"" ++ nl ++
"type Nat" ++ nl ++
"  = O" ++ nl ++
"  | S Nat" ++ nl ++
"" ++ nl ++
"foo : Sig Nat □" ++ nl ++
"foo =" ++ nl ++
"  Exist O" ++ nl ++
"" ++ nl ++
"bar : Nat" ++ nl ++
"bar =" ++ nl ++
"  proj1_sig foo".
  Check eq_refl : ltac:(let x := eval vm_compute in (extract ex1) in exact x) =
                  Ok ex1_expected.
End ex1.

Module ex2.
  Definition only_in_type := 5.
  Definition foo : { n : nat | only_in_type = 5 } := exist _ 0 eq_refl.
  Definition bar := proj1_sig foo.
  MetaCoq Quote Recursively Definition ex2 := bar.
  Check eq_refl : ltac:(let x := eval vm_compute in (extract ex2) in exact x) =
                  Ok ex1.ex1_expected.
End ex2.

Module ex3.
  Definition foo (f : 5 = 5 -> nat -> nat) := f eq_refl 0.
  Definition bar (p : 5 = 5) (n : nat) := n.
  (* bar must be eta expanded in the following *)
  Definition baz := foo bar.
  MetaCoq Quote Recursively Definition ex3 := baz.

  Definition ex3_expected :=
"type Nat" ++ nl ++
"  = O" ++ nl ++
"  | S Nat" ++ nl ++
"" ++ nl ++
"foo : (□ -> Nat -> Nat) -> Nat" ++ nl ++
"foo f =" ++ nl ++
"  f □ O" ++ nl ++
"" ++ nl ++
"bar : Nat -> Nat" ++ nl ++
"bar n =" ++ nl ++
"  n" ++ nl ++
"" ++ nl ++
"baz : Nat" ++ nl ++
"baz =" ++ nl ++
"  foo (\x -> bar)".
  Check eq_refl : ltac:(let x := eval vm_compute in (extract ex3) in exact x) =
                  Ok ex3_expected.
End ex3.

Module ex4.
  Definition foo : {0 = 0} + {0 <> 0} := left eq_refl.
  MetaCoq Quote Recursively Definition ex4 := foo.

  Definition ex4_expected :=
"type Sumbool a b" ++ nl ++
"  = Left" ++ nl ++
"  | Right" ++ nl ++
"" ++ nl ++
"foo : Sumbool □ □" ++ nl ++
"foo =" ++ nl ++
"  Left".
  Check eq_refl : ltac:(let x := eval vm_compute in (extract ex4) in exact x) =
                  Ok ex4_expected.
End ex4.

Module ex5.
  (* Using normal sum means it cannot be deboxed away *)
  Definition foo : (0 = 0) + (0 <> 0) := inl eq_refl.
  MetaCoq Quote Recursively Definition ex5 := foo.

  Definition ex5_expected :=
"type Sum a b" ++ nl ++
"  = Inl a" ++ nl ++
"  | Inr b" ++ nl ++
"" ++ nl ++
"foo : Sum □ □" ++ nl ++
"foo =" ++ nl ++
"  Inl □".
  Check eq_refl : ltac:(let x := eval vm_compute in (extract ex5) in exact x) =
                  Ok ex5_expected.
End ex5.

Module ex6.
  Definition foo (f : 5 = 5 -> 5 = 5 -> nat -> nat) := f eq_refl eq_refl 0.
  Definition bar (m : nat) (p q : 5 = 5) (n : nat) := m + n.
  (* bar must be eta expanded twice and m and n need to be lifted *)
  Definition baz := (fun m n => foo (bar (m + n))) 0.
  MetaCoq Quote Recursively Definition ex6 := baz.

  Definition ex6_expected :=
"type Nat" ++ nl ++
"  = O" ++ nl ++
"  | S Nat" ++ nl ++
"" ++ nl ++
"foo : (□ -> □ -> Nat -> Nat) -> Nat" ++ nl ++
"foo f =" ++ nl ++
"  f □ □ O" ++ nl ++
"" ++ nl ++
"add : Nat -> Nat -> Nat" ++ nl ++
"add n m =" ++ nl ++
"  case n of" ++ nl ++
"    O ->" ++ nl ++
"      m" ++ nl ++
"    S p ->" ++ nl ++
"      S (add p m)" ++ nl ++
"" ++ nl ++
"bar : Nat -> Nat -> Nat" ++ nl ++
"bar m n =" ++ nl ++
"  add m n" ++ nl ++
"" ++ nl ++
"baz : Nat -> Nat" ++ nl ++
"baz =" ++ nl ++
"  (\m n -> foo (\x x2 -> bar (add m n))) O".
  Check eq_refl : ltac:(let x := eval vm_compute in (extract ex6) in exact x) =
                  Ok ex6_expected.
End ex6.

Module ex7.
  (* Dearg through lets *)
  Definition foo (n : nat) (x := 0) (p : x = 0) (m : nat) := match n with 0 => m | _ => n end.
  Definition bar := foo 1 eq_refl 0.
  MetaCoq Quote Recursively Definition ex7 := bar.

  Definition ex7_expected :=
"type Nat" ++ nl ++
"  = O" ++ nl ++
"  | S Nat" ++ nl ++
"" ++ nl ++
"foo : Nat -> Nat -> Nat" ++ nl ++
"foo n =" ++ nl ++
"  let" ++ nl ++
"    x =" ++ nl ++
"      O" ++ nl ++
"  in" ++ nl ++
"  \m -> case n of" ++ nl ++
"          O ->" ++ nl ++
"            m" ++ nl ++
"          S n0 ->" ++ nl ++
"            n" ++ nl ++
"" ++ nl ++
"bar : Nat" ++ nl ++
"bar =" ++ nl ++
"  foo (S O) O".
  Check eq_refl : ltac:(let x := eval vm_compute in (extract ex7) in exact x) =
                  Ok ex7_expected.
End ex7.

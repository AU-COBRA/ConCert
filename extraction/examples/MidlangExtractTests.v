(** * Tests for extraction to Midlang *)
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

Instance StandardBoxes : BoxSymbol :=
  {| term_box_symbol := "□";
     type_box_symbol := "□";
     any_type_symbol := "𝕋"|}.

Definition general_extract (p : program) (ignore: list kername) (TT : list (kername * string)) : result string string :=
  entry <- match p.2 with
           | tConst kn _ => ret kn
           | _ => Err "Expected program to be a tConst"
           end;;
  Σ <- specialize_erase_debox_template_env p.1 [entry] ignore;;
  let TT_fun kn := option_map snd (List.find (fun '(kn',v) => eq_kername kn kn') TT) in
  '(_, s) <- finish_print (print_env Σ p.1 TT_fun);;
  ret s.

Definition extract (p : program) : result string string :=
  general_extract p [] [].


Module ex1.
  Definition foo : { n : nat | n = 0 } := exist _ 0 eq_refl.
  Definition bar := proj1_sig foo.
  MetaCoq Quote Recursively Definition ex1 := bar.

  Definition ex1_expected :=
"type Sig a" ++ nl ++
"  = Exist a" ++ nl ++
"" ++ nl ++
"proj1_sig : Sig a -> a" ++ nl ++
"proj1_sig e =" ++ nl ++
"  case e of" ++ nl ++
"    Exist a ->" ++ nl ++
"      a" ++ nl ++
"" ++ nl ++
"type Nat" ++ nl ++
"  = O" ++ nl ++
"  | S Nat" ++ nl ++
"" ++ nl ++
"foo : Sig Nat" ++ nl ++
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
"  foo (\_ -> bar)".
  Check eq_refl : ltac:(let x := eval vm_compute in (extract ex3) in exact x) =
                  Ok ex3_expected.
End ex3.

Module ex4.
  Definition foo : {0 = 0} + {0 <> 0} := left eq_refl.
  MetaCoq Quote Recursively Definition ex4 := foo.

  Definition ex4_expected :=
"type Sumbool" ++ nl ++
"  = Left" ++ nl ++
"  | Right" ++ nl ++
"" ++ nl ++
"foo : Sumbool" ++ nl ++
"foo =" ++ nl ++
"  Left".

  Check eq_refl : ltac:(let x := eval vm_compute in (extract ex4) in exact x) =
                  Ok ex4_expected.
End ex4.

Module ex5.
  (* Using normal sum means it cannot be deboxed away *)
  Definition foo : (0 = 0) + (0 <> 0) := inl eq_refl.
  MetaCoq Quote Recursively Definition ex5 := foo.
  Compute extract ex5.

  Definition ex5_expected :=
"type Sum a b" ++ nl ++
"  = Inl a" ++ nl ++
"  | Inr b" ++ nl ++
"" ++ nl ++
"foo : Sum □ □" ++ nl ++
"foo =" ++ nl ++
"  Inl □".
  Compute (extract ex5).
  Compute ex5_expected.
  Check eq_refl : ltac:(let x := eval vm_compute in (extract ex5) in exact x) =
                  Ok ex5_expected.
End ex5.

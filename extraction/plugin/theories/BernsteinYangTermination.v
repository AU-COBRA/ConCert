(* Computation needed to show termination of the Bernstein-Yang modular inversion algorithm *)

From ConCert.Extraction Require Import Loader.
From Coq Require Import Arith.
From Coq Require Import Bool.
From Coq Require Import Extraction.
From Coq Require Import List.
From Coq Require Import Program.
From Coq Require Import ZArith.

Import ListNotations.

Import Z.
Local Open Scope Z.
Definition steps := Eval vm_compute in 2 ^ 44 : N.
Definition shiftl a b := Eval cbv in Z.shiftl a b.
Definition shiftr a b := Eval cbv in Z.shiftr a b.
Definition divstep d f g :=
  if (0 <? d) && odd g
  then (1 - d, g, shiftr (g - f) 1)
  else (1 + d, f, shiftr (g + (if odd g then 1 else 0) * f) 1 ).
Fixpoint needs_n_steps (d a b : Z) n :=
  match n with
  | 0%nat => true
  | S n => if (b =? 0)
          then false
          else let '(d', a', b') := divstep d a b in needs_n_steps d' a' b' n
  end.
Fixpoint min_needs_n_steps_nat (a b : Z) n (acc : Z) fuel :=
  match fuel with
  | 0%nat => 0
  | S fuel =>
    let a2 := a * a in
    if acc <? a2
        then acc
        else
          let length := a2 + b * b in
          if acc <? length
             then min_needs_n_steps_nat (a + 2) 0 n acc fuel
             else if needs_n_steps 1 a (shiftr b 1) n || needs_n_steps 1 a (- (shiftr b 1)) n
                  then min_needs_n_steps_nat (a + 2) 0 n (min length acc) fuel
                  else min_needs_n_steps_nat a (b + 2) n acc fuel
  end.
Definition nat_shiftl := Eval cbv in Nat.shiftl.
Definition W n := min_needs_n_steps_nat 1 0 n (shiftl 1 62) (nat_shiftl 1 44).

Extract Constant nat_shiftl => "fn ##name##(&'a self, a: u64, b: u64) -> u64 { a << b }".
(* Unsound in general, but fine for this program *)
Extract Constant shiftl => "fn ##name##(&'a self, a: i64, b: i64) -> i64 { a << b }".
Extract Constant shiftr => "fn ##name##(&'a self, a: i64, b: i64) -> i64 { a >> b }".

From ConCert.Extraction Require Import ExtrRustBasic.
From ConCert.Extraction Require Import ExtrRustUncheckedArith.
Redirect "../examples/extracted-code/rust-extract/BernsteinYangTermination.rs" ConCert Extract W.

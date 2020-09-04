From Coq Require Import PeanoNat ZArith Notations Bool.

From MetaCoq.Template Require Import Loader.
From MetaCoq.Erasure Require Import SafeTemplateErasure Loader.
From MetaCoq.Erasure Require ErasureFunction.
From MetaCoq.Erasure Require SafeErasureFunction.
From MetaCoq.Template Require Import config.
From MetaCoq.SafeChecker Require Import PCUICSafeReduce PCUICSafeChecker
     SafeTemplateChecker.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICTyping
     TemplateToPCUIC.

From ConCert.Embedding Require Import MyEnv.
From ConCert.Extraction Require Import LiquidityExtract LPretty Common.

From Coq Require Import List String.

From MetaCoq.Template Require Import All.

Import ListNotations.
Import MonadNotation.

Open Scope nat.

Definition rank2_ex : forall (A : Type), A -> (forall A : Type, A -> A) -> A :=
fun A a f => f _ a.
Extraction rank2_ex.

(** Cumulativity *)
Definition const_zero {A : Type} (a : A) := 0.

Definition const_zero_app_prop := const_zero True.
Definition const_zero_app_type := const_zero 0.

MetaCoq Erase (unfolded const_zero_app_prop).
MetaCoq Erase (unfolded const_zero_app_type).

Definition weird_map {A B} (f : A -> B) (l : list A) : unit -> list B :=
  let g := @map A in
  fun _ : unit => g B f l.

MetaCoq Erase (unfolded @weird_map).

Definition ex_prop (n : nat) (p : (0 < n)%nat) := n.

(** Let's return something more tricky that could not be optimised easily *)
Definition ex3 (n : nat) (b : bool) :=
  let f := match b with | true => ex_prop (S n) | false => fun _ => 0 end in
  fun _ : unit => f (Nat.lt_0_succ n) + f (Nat.lt_0_succ n).

MetaCoq Erase (unfolded ex3).
Extraction ex3.

Definition ex4 (n : nat) (b : bool) :=
  (match b with
  | true => (fun (p : 0 < S n) => n)
  | false => fun _ => 0
  end) (Nat.lt_0_succ n).

MetaCoq Erase (unfolded ex4).

Definition erase_print_with_boxes (p : Ast.program) : string :=
  let p := fix_program_universes p in
  let checked_t := erase_template_program p in
  let res := print_EnvCheck (fun Σ t => EPretty.print_term Σ [] true false t) checked_t in
  print_sum res.

Definition erase_print_deboxed_all_applied (p : Ast.program) : string :=
  let p := fix_program_universes p in
  let deboxed := erase_debox_all_applied [] p in
  let res := print_EnvCheck (fun Σ t => EPretty.print_term Σ [] true false t) deboxed in
  print_sum res.

Quote Recursively Definition fold_left_prog := (unfolded fold_left).
Compute erase_print_with_boxes fold_left_prog.

Quote Recursively Definition map_prog := (unfolded map).
Compute erase_print_with_boxes map_prog.

Definition sum_nat (xs : list nat) : nat := fold_left plus xs 0.

Set Printing Implicit.
Print sum_nat.
Unset Printing Implicit.

Quote Recursively Definition sum_prog := (unfolded sum_nat).

Compute erase_print_with_boxes sum_prog.

Definition square (xs : list nat) : list nat := map (fun x => x * x) xs.

Quote Recursively Definition square_prog := (unfolded square).
Compute erase_print_with_boxes square_prog.
Compute erase_print_deboxed_all_applied square_prog.

Definition local_def := local "".

(** A translation table for various constants we want to rename *)
Definition TT : env string :=
  [  remap <% List.map %> "List.map" ;
     remap <% Nat.mul %> "mulNat" ;
     remap <% nat %> "nat" ;
     remap <% list %> "list"].

Quote Recursively Definition square_syn := (unfolded square).

Time Run TemplateProgram
     (t1 <- toLiquidity "" TT square ;;
      tmPrint t1).

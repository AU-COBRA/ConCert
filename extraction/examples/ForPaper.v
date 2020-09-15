From Coq Require Import PeanoNat ZArith Notations Bool.

From ConCert.Embedding Require Import MyEnv.
From ConCert.Extraction Require Import Common.
From ConCert.Extraction Require Import MidlangExtract.
From ConCert.Extraction Require Import LiquidityExtract.
From ConCert.Extraction Require Import Optimize.
From ConCert.Extraction Require Import Erasure.
From ConCert.Extraction Require Import ResultMonad.

From MetaCoq.Template Require Import Loader.
From MetaCoq.Erasure Require Import SafeTemplateErasure Loader.
From MetaCoq.Erasure Require ErasureFunction.
From MetaCoq.Erasure Require SafeErasureFunction.
From MetaCoq.Erasure Require EPretty.
From MetaCoq.Template Require Import config.
From MetaCoq.SafeChecker Require Import PCUICSafeReduce PCUICSafeChecker
     SafeTemplateChecker.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICTyping
     TemplateToPCUIC.


From Coq Require Import List String.

From MetaCoq.Template Require Import All.

Import ListNotations.
Import MonadNotation.
Import ResultMonad.

Open Scope nat.

Definition rank2_ex : forall (A : Type), A -> (forall A : Type, A -> A) -> A :=
fun A a f => f _ a.
Extraction rank2_ex.

(** ** Cumulativity *)

(** The [sum] type constructor can be instantiated with Prop *)
Definition inl_prop : Prop + Prop:= @inl Prop Prop True.

MetaCoq Erase (unfolded inl_prop).
(* Environment is well-formed and [inl [Prop] [Prop]] True erases to:
   inl ∎ ∎ ∎ *)
(** We cannot remove all boxes from [inl ∎ ∎ ∎ ] because we it won't match with deboxing of the
    definition of the [sum] type. *)

(** For other instantiations the last parameter is relevant and will not be erased. *)
Definition inl_type : nat + bool:= @inl _ _ 0.
MetaCoq Erase (unfolded inl_type).
(* Environment is well-formed and [inl nat bool O] erases to:
   inl ∎ ∎ O *)

(** Therefore, the best we can do is to keep the last box in the erased version of [inl_prop]:
    [inl ∎ ∎ ∎] *)

(** The similar things happen to polymorphic constants *)
Definition const_zero {A : Type} (a : A) := 0.

Definition const_zero_app_prop := const_zero True.
Definition const_zero_app_type := const_zero 0.

MetaCoq Erase (unfolded const_zero_app_prop).
(* const_zero ∎ ∎ *)
MetaCoq Erase (unfolded const_zero_app_type).
(* const_zero ∎ O *)

Definition erase_print (p : program) (debox : bool) : result string string :=
  entry <- match p.2 with
           | tConst kn _ => ret kn
           | _ => Err "Expected program to be a tConst"
          end;;
  Σ <- general_specialize_erase_debox_template_env p.1 [entry] (fun kn' => negb ( eq_kername entry kn')) false debox ;;
  decl <- result_of_option (ExAst.lookup_env Σ entry) "Error : no declaration found" ;;
  match decl with
  | ExAst.ConstantDecl cb =>
    b <- result_of_option cb.(ExAst.cst_body) "Error: a constant with no body";;
    ret (EPretty.print_term (Common.trans_global_decls Σ) [] true false b)
  | _ => Err "Error: expected a constant"
  end.

Definition sum_nat (xs : list nat) : nat := fold_left plus xs 0.

Set Printing Implicit.
Print sum_nat.
(* sum_nat = fun xs : list nat => @fold_left nat nat Init.Nat.add xs 0
     : list nat -> nat *)
Unset Printing Implicit.

MetaCoq Quote Recursively Definition sum_prog := sum_nat.

(** Erase and print before the deboxing step *)
Compute erase_print sum_prog false.
(* = Ok "fun xs => Coq.Lists.List.fold_left ∎ ∎ Coq.Init.Nat.add xs O" *)

(** Erase and print after the deboxing step *)
Compute erase_print sum_prog true.
(* = Ok "fun xs => Coq.Lists.List.fold_left Coq.Init.Nat.add xs O" *)

Definition square (xs : list nat) : list nat := map (fun x => x * x) xs.

MetaCoq Quote Recursively Definition square_prog := square.

(** Erase and print before the deboxing step *)
Compute erase_print square_prog false.
(* = Ok "fun xs => Coq.Lists.List.map ∎ ∎ (fun x => Coq.Init.Nat.mul x x) xs" *)

(** Erase and print after the deboxing step *)
Compute erase_print square_prog true.
(* = Ok "fun xs => Coq.Lists.List.map (fun x => Coq.Init.Nat.mul x x) xs" *)


(** A translation table for various constants we want to rename *)
Definition TT :=
  [  remap <% List.map %> "Liquidity.List.map" ;
     remap <% Nat.mul %> "mulNat" ;
     remap <% nat %> "nat" ;
     remap <% list %> "list"].

MetaCoq Quote Recursively Definition square_syn := square.

(** Erase and print the program give the remapped definitions *)
Time Compute liquitidy_simple_extract TT [] false square_syn.
(* = inl "let square (xs : ( (nat) list)) = Liquidity.List.map (fun x -> mulNat x x) xs" *)

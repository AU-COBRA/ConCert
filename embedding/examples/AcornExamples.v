(** * Examples of library code and contracts originating
      from the actual Acorn implementation *)
From MetaRocq.Template Require Import All.
From ConCert.Embedding Require Import Ast.
From ConCert.Embedding Require Import Notations.
From ConCert.Embedding Require Import PCUICTranslate.
From ConCert.Embedding Require Import PCUICtoTemplate.
From ConCert.Embedding Require Import TranslationUtils.
From Stdlib Require Import ZArith.
From Stdlib Require Import Basics.
From Stdlib Require Import String.
From Stdlib Require Import List.
From Stdlib Require Import PeanoNat.

Import MRMonadNotation.
Import ListNotations.

Open Scope list.

(** All ASTs below were produced by a printing function implemented in
    Haskell and operating on Haskell representation of Acorn terms.
    We collect the outputs of our printing procedure for several modules
    in this Rocq file. For the [ListBase] example, we give also a
    corresponding Acorn source code *)

(** ** [Bool] module from the standard library of Acorn *)
Module AcornBool.
  MetaRocq Run define_mod_prefix.

  Definition Data := [gdInd "Bool" 0 [("True_rocq", []); ("False_rocq", [])] false].
  (*---------------------*)
  Definition Functions := [
    ("not", eLambda "x"
                    (tyInd "Bool")
                    (eCase ("Bool", [])
                           (tyInd "Bool")
                           (eRel 0)
                           [(pConstr "True_rocq" [], eConstr "Bool" "False_rocq");
                            (pConstr "False_rocq" [], eConstr "Bool" "True_rocq")]))].

  MetaRocq Run (translateData [] Data).

  MetaRocq Run (translateDefs [] Data Functions).
End AcornBool.

(** ** [Maybe] module from the standard library of Acorn *)

Module AcornMaybe.
  MetaRocq Run define_mod_prefix.

  Definition Data := [gdInd "Maybe" 1 [("Nothing_rocq", []);
                                       ("Just_rocq", [(None, tyRel 0)])] false].
  (*---------------------*)
  Definition Functions := [
    ("isJust", eTyLam "A"
                (eLambda "x"
                  (tyApp (tyInd "Maybe") (tyRel 0))
                  (eCase ("Maybe",[tyRel 0])
                    (tyInd "Bool")
                    (eRel 0)
                    [(pConstr "Nothing_rocq" [], eConstr "Bool" "False_rocq");
                    (pConstr "Just_rocq" ["x0"], eConstr "Bool" "True_rocq")])))].

  MetaRocq Run (translateData [] Data).
  MetaRocq Run (translateDefs AcornBool.exported (Data ++ AcornBool.Data) Functions).

End AcornMaybe.

Import AcornMaybe.

(** ** Acorn pairs *)
Module AcornProd.

  Definition Data := [gdInd "Pair" 2 [("Pair_rocq", [(None, tyRel 1);
                                                    (None, tyRel 0)])] false].
  (*---------------------*)

  Definition Functions :=
    [("fst", eTyLam "A"
              (eTyLam "A"
                (eLambda "x"
                  (tyApp (tyApp (tyInd "Pair") (tyRel 1)) (tyRel 0))
                  (eCase ("Pair",[(tyRel 1); (tyRel 0)])
                    (tyRel 1)
                    (eRel 0)
                    [(pConstr "Pair_rocq" ["x0"; "x1"], eRel 1)]))));
     ("snd", eTyLam "A"
              (eTyLam "A"
                (eLambda "x"
                  (tyApp (tyApp (tyInd "Pair") (tyRel 1)) (tyRel 0))
                  (eCase ("Pair",[(tyRel 1); (tyRel 0)])
                    (tyRel 0)
                    (eRel 0)
                    [(pConstr "Pair_rocq" ["x0"; "x1"], eRel 0)]))))].

  MetaRocq Run (translateData [] Data).

  MetaRocq Run (translateDefs [] Data Functions).
End AcornProd.

(** ** Acorn [List] module *)

(** We consider the example of verifying certain functions on Acorn
    lists in the paper. We provide a full source code for the Acorn
    [ListBase] we translated *)

(*
module ListBase where

import Prod
import Bool

data List a = Nil [] | Cons [a, (List a)]

definition singleton a (x :: a) = Cons [a] x (Nil [a])

definition foldr a b (f :: a -> b -> b) (initVal :: b) =
  letrec go (xs :: List a) :: b =
         case xs of
            Nil -> initVal
            Cons x xs' -> f x (go xs')
  in go


definition map a b (f :: a -> b) =
    foldr [a] [List b] (fun (x :: a) = Cons [b] (f x)) (Nil [b])


-- This definition corresponds to fold_left from the Rocq's StdLib.
-- Recursion is on the first argument.
   This is the only case handled by Acorn -> Rocq translation.
definition foldl_alt a b (f :: b -> a -> b) =
  letrec go (xs :: List a) (acc :: b) :: b =
     case xs of
       Nil -> acc
       Cons x xs' -> go xs' (f acc x)
  in go

definition foldl a b (f :: b -> a -> b) (x :: b) (xs :: List a) = foldl_alt [a] [b] f xs x

definition concat a (xs :: List a) (ys :: List a) =
   foldr [a] [List a] (Cons [a]) ys xs

definition zipWith a b c (f :: a -> b -> c) =
  letrec go (xs :: List a) :: (List b -> List c) =
    fun (ys :: List b) = case xs of
                           Nil -> Nil [c]
                           Cons x xs' -> case ys of
                                           Nil -> Nil [c]
                                           Cons y ys' -> Cons [c] (f x y) (go xs' ys')
  in go

definition reverse a =
   foldl [a] [List a] (fun (xs :: List a) (x :: a) = Cons [a] x xs) (Nil [a])

definition zip a b = zipWith [a] [b] [Prod.Pair a b] (Prod.Pair [a] [b])

definition filter a (p :: a -> Bool.Bool) =
  foldr [a] [List a] (fun (x :: a) (xs :: List a) =
      case p x of
        Bool.True -> Cons [a] x xs
        Bool.False -> xs) (Nil [a])
*)
Module AcornListBase.
  Import AcornBool.
  Import AcornProd.

  Definition Data := [
    gdInd "List"
      1
      [("Nil_rocq", []);
      ("Cons_rocq", [(None, tyRel 0); (None, (tyApp (tyInd "List") (tyRel 0)))])] false].

  (*---------------------*)
  Definition Functions :=
  [ ("singleton", eTyLam "A"
      (eLambda "x"
        (tyRel 0)
        (eApp
          (eApp
            (eApp
              (eConstr "List" "Cons_rocq")
              (eTy (tyRel 0)))
            (eRel 0))
          (eApp
            (eConstr "List" "Nil_rocq")
            (eTy (tyRel 0))))))
  ; ("foldr", eTyLam "A"
      (eTyLam "A"
        (eLambda "x"
          (tyArr
            (tyRel 1)
            (tyArr (tyRel 0) (tyRel 0)))
          (eLambda "x"
            (tyRel 0)
            (eLetIn "f"
              (eFix "rec" "x"
                (tyApp (tyInd "List") (tyRel 1))
                (tyRel 0)
                (eCase
                  ("List", [tyRel 1])
                  (tyRel 0)
                  (eRel 0)
                  [(pConstr "Nil_rocq" [], eRel 2);
                  (pConstr "Cons_rocq" ["x0"; "x1"],
                   eApp
                    (eApp (eRel 5) (eRel 1))
                    (eApp (eRel 3) (eRel 0)))]))
              (tyArr
                (tyApp (tyInd "List") (tyRel 1))
                (tyRel 0))
              (eRel 0))))))
  ; ("map", eTyLam "A"
      (eTyLam "A"
        (eLambda "x"
          (tyArr (tyRel 1) (tyRel 0))
          (eApp
            (eApp
              (eApp
                (eApp (eConst "foldr") (eTy (tyRel 1)))
                (eTy (tyApp (tyInd "List") (tyRel 0))))
              (eLambda "x"
                (tyRel 1)
                (eApp
                  (eApp (eConstr "List" "Cons_rocq") (eTy (tyRel 0)))
                  (eApp (eRel 1) (eRel 0)))))
            (eApp
              (eConstr "List" "Nil_rocq")
              (eTy (tyRel 0)))))))
  ; ("foldl_alt", eTyLam "A"
      (eTyLam "A"
        (eLambda "x"
          (tyArr (tyRel 0) (tyArr (tyRel 1) (tyRel 0)))
          (eLetIn "f"
            (eFix "rec" "x"
              ((tyApp (tyInd "List") (tyRel 1)))
              (tyArr (tyRel 0) (tyRel 0))
              (eLambda "x"
                (tyRel 0)
                (eCase
                  ("List", [tyRel 1])
                  (tyRel 0)
                  (eRel 1)
                  [(pConstr "Nil_rocq" [], eRel 0);
                   (pConstr "Cons_rocq" ["x0"; "x1"],
                   eApp
                    (eApp (eRel 4) (eRel 0))
                    (eApp
                      (eApp (eRel 5) (eRel 2))
                      (eRel 1)))])))
              (tyArr
                (tyApp (tyInd "List") (tyRel 1))
                (tyArr (tyRel 0) (tyRel 0))) (eRel 0)))))
  ; ("foldl", eTyLam "A"
      (eTyLam "A"
        (eLambda "x"
          (tyArr
            (tyRel 0)
            (tyArr (tyRel 1) (tyRel 0)))
          (eLambda "x"
            (tyRel 0)
            (eLambda "x"
              (tyApp (tyInd "List") (tyRel 1))
              (eApp
                (eApp
                  (eApp
                    (eApp
                      (eApp
                        (eConst "foldl_alt")
                        (eTy (tyRel 1)))
                      (eTy (tyRel 0)))
                    (eRel 2))
                  (eRel 0))
                (eRel 1)))))))
  ; ("concat", eTyLam "A"
      (eLambda "x"
        (tyApp (tyInd "List") (tyRel 0))
        (eLambda "x"
          (tyApp (tyInd "List") (tyRel 0))
          (eApp
            (eApp
              (eApp
                (eApp
                  (eApp (eConst "foldr") (eTy (tyRel 0)))
                  (eTy (tyApp (tyInd "List") (tyRel 0))))
                (eApp
                  (eConstr "List" "Cons_rocq")
                  (eTy (tyRel 0))))
              (eRel 0))
            (eRel 1)))))
  ; ("zipWith", eTyLam "A"
      (eTyLam "A"
        (eTyLam "A"
          (eLambda "x"
            (tyArr
              (tyRel 2)
              (tyArr (tyRel 1) (tyRel 0)))
            (eLetIn "f"
              (eFix "rec" "x"
                (tyApp (tyInd "List") (tyRel 2))
                (tyArr
                  (tyApp (tyInd "List") (tyRel 1))
                  (tyApp (tyInd "List") (tyRel 0)))
                (eLambda "x"
                  (tyApp (tyInd "List") (tyRel 1))
                  (eCase
                    ("List", [tyRel 2])
                    (tyApp (tyInd "List") (tyRel 0))
                    (eRel 1)
                    [(pConstr "Nil_rocq" [],
                      eApp (eConstr "List" "Nil_rocq") (eTy (tyRel 0)));
                     (pConstr "Cons_rocq"
                        ["x0"; "x1"],
                      eCase
                        ("List", [tyRel 1])
                        (tyApp (tyInd "List") (tyRel 0))
                        (eRel 2)
                        [(pConstr "Nil_rocq" [],
                          eApp (eConstr "List" "Nil_rocq") (eTy (tyRel 0)));
                         (pConstr "Cons_rocq" ["x0"; "x1"],
                          eApp
                            (eApp
                              (eApp
                                (eConstr "List" "Cons_rocq")
                                (eTy (tyRel 0)))
                              (eApp
                                (eApp (eRel 7) (eRel 3))
                                (eRel 1)))
                            (eApp
                              (eApp (eRel 6) (eRel 2))
                              (eRel 0)))])])))
              (tyArr
                (tyApp (tyInd "List") (tyRel 2))
                (tyArr
                  (tyApp (tyInd "List") (tyRel 1))
                  (tyApp (tyInd "List") (tyRel 0))))
              (eRel 0))))))
  ; ("reverse", eTyLam "A"
      (eApp
        (eApp
          (eApp
            (eApp
              (eConst "foldl")
              (eTy (tyRel 0)))
            (eTy
              (tyApp (tyInd "List") (tyRel 0))))
          (eLambda "x"
            (tyApp (tyInd "List") (tyRel 0))
            (eLambda "x"
              (tyRel 0)
              (eApp
                (eApp
                  (eApp
                    (eConstr "List" "Cons_rocq")
                    (eTy (tyRel 0)))
                  (eRel 0))
                (eRel 1)))))
        (eApp
          (eConstr "List" "Nil_rocq")
          (eTy (tyRel 0)))))
  ; ("zip", eTyLam "A"
      (eTyLam "A"
        (eApp
          (eApp
            (eApp
              (eApp
                (eConst "zipWith")
                (eTy (tyRel 1)))
              (eTy (tyRel 0)))
            (eTy
              (tyApp
                (tyApp (tyInd "Pair") (tyRel 1))
                (tyRel 0))))
          (eApp
            (eApp
              (eConstr "Pair" "Pair_rocq")
              (eTy (tyRel 1)))
            (eTy (tyRel 0))))))
  ; ("filter", eTyLam "A"
      (eLambda "x"
        (tyArr
          (tyRel 0)
          ((tyInd "Bool")))
        (eApp
          (eApp
            (eApp
              (eApp
                (eConst "foldr")
                (eTy (tyRel 0)))
              (eTy (tyApp (tyInd "List") (tyRel 0))))
            (eLambda "x"
              (tyRel 0)
              (eLambda "x"
                (tyApp (tyInd "List") (tyRel 0))
                (eCase
                  ("Bool", [])
                  (tyApp (tyInd "List") (tyRel 0))
                  (eApp (eRel 2) (eRel 1))
                  [(pConstr "True_rocq" [],
                    eApp
                      (eApp
                        (eApp
                          (eConstr "List" "Cons_rocq")
                          (eTy (tyRel 0)))
                        (eRel 1))
                      (eRel 0));
                   (pConstr "False_rocq" [], eRel 0)]))))
          (eApp
            (eConstr "List" "Nil_rocq")
            (eTy (tyRel 0))))))
  ].

  MetaRocq Run (translateData [] Data).

  Definition gEnv := (Data ++ AcornBool.Data ++ AcornProd.Data)%list.

  Definition dependencies := AcornBool.exported ++ AcornProd.exported.

  MetaRocq Run (translateDefs dependencies gEnv Functions).

  Definition AcornList := List.

  (** We prove that the imported definitions are equivalent to the
      corresponding definitions from the standard library of Rocq *)
  Fixpoint from_acorn {A : Set} (acornL : AcornList A) : list A :=
    match acornL with
    | Cons_rocq hd tl => hd :: from_acorn tl
    | Nil_rocq => []
    end.

  Fixpoint to_acorn {A : Set} (rocqL : list A) : AcornList A :=
    match rocqL with
    | hd :: tl => Cons_rocq _ hd (to_acorn tl)
    | nil => Nil_rocq _
    end.

  Lemma to_from_acorn (A : Set) (l : AcornList A) : to_acorn (from_acorn l) = l.
  Proof.
    induction l; simpl; congruence.
  Qed.

  Lemma from_to_acorn (A : Set) (l : list A) : from_acorn (to_acorn l) = l.
  Proof.
    induction l; simpl; congruence.
  Qed.

  Arguments foldr {_ _}.
  Arguments concat {_}.

  Lemma acorn_foldr_rocq_fold_right (A B : Set) (l : AcornList A) (f : A -> B -> B) a :
    foldr f a l = fold_right f a (from_acorn l).
  Proof.
    induction l; simpl; auto.
    f_equal. congruence.
  Qed.

  Open Scope list.

  Lemma concat_app (A : Set) (l1 l2 : AcornList A) :
  concat l1 l2 = to_acorn (from_acorn l1 ++ from_acorn l2).
  Proof.
    revert l2.
    induction l1; intros l2; destruct l2; simpl; try rewrite to_from_acorn; auto.
    f_equal. rewrite app_nil_r. rewrite to_from_acorn.
    clear IHl1; induction l1; simpl. congruence. now f_equal.
    change (a0 :: from_acorn l2) with (from_acorn (Cons_rocq _ a0 l2)).
    now f_equal.
  Qed.

  #[local]
  Hint Rewrite acorn_foldr_rocq_fold_right concat_app from_to_acorn : hints.

  Lemma concat_assoc :
    forall (A : Set) (l m n : AcornList A), concat l (concat m n) = concat (concat l m) n.
  Proof.
    intros. autorewrite with hints. f_equal.
    apply app_assoc.
  Qed.

  Lemma foldr_concat (A B : Set) (f : A -> B -> B) (l l' : AcornList A) (i : B) :
      foldr f i (concat l l') = foldr f (foldr f i l') l.
  Proof. autorewrite with hints; apply fold_right_app. Qed.

End AcornListBase.

(** ** Acorn blockchain-related data types *)
Module AcornBlochain.

  Definition ABl_data := [
    gdInd "Caller" 0
      [("CallerContract_rocq", [(None, tyInd "nat")]);
       ("CallerAccount_rocq", [(None, tyInd "string")])] false;
    gdInd "ChainContext" 0
      [("ChainContext_rocq",
        [(None, tyInd "nat");
         (None, tyInd "nat");
         (None, tyInd "nat")])] false;
    gdInd "InitContext" 0
      [("InitContext_rocq",
        [(None, (tyInd "ChainContext"));
         (None, tyInd "string")])] false;
    gdInd "ReceiveContext" 0
      [("ReceiveContext_rocq",
        [(None, (tyInd "ChainContext"));
         (None, tyInd "string");
         (None, tyInd "nat")])] false
  ].
  (*---------------------*)
  Definition ABl_functions :=
    [ ("slotNumber", eLambda "x"
        (tyInd "ChainContext")
        (eCase
          ("ChainContext", [])
          (tyInd "nat")
          (eRel 0)
          [(pConstr "ChainContext_rocq" ["x0"; "x1"; "x2"], eRel 2)]))
    ; ("blockHeight", eLambda "x"
        (tyInd "ChainContext")
        (eCase
          ("ChainContext", [])
          (tyInd "nat")
          (eRel 0)
          [(pConstr "ChainContext_rocq" ["x0"; "x1"; "x2"], eRel 1)]))
    ; ("finalizedHeight", eLambda "x"
        (tyInd "ChainContext")
        (eCase
          ("ChainContext", [])
          (tyInd "nat")
          (eRel 0)
          [(pConstr "ChainContext_rocq" ["x0"; "x1"; "x2"], eRel 0)]))
    ; ("initOrigin", eLambda "x"
        (tyInd "InitContext")
        (eCase
          ("InitContext", [])
          (tyInd "string")
          (eRel 0)
          [(pConstr "InitContext_rocq" ["x0"; "x1"], eRel 0)]))
    ; ("initChain", eLambda "x"
        (tyInd "InitContext")
        (eCase
          ("InitContext", [])
          (tyInd "ChainContext")
          (eRel 0)
          [(pConstr "InitContext_rocq" ["x0"; "x1"], eRel 1)]))
    ; ("receiveChain", eLambda "x"
        (tyInd "ReceiveContext")
        (eCase
          ("ReceiveContext", [])
          (tyInd "ChainContext")
          (eRel 0)
          [(pConstr "ReceiveContext_rocq" ["x0"; "x1"; "x2"], eRel 2)]))
    ; ("receiveOrigin", eLambda "x"
        (tyInd "ReceiveContext")
        (eCase
          ("ReceiveContext", [])
          (tyInd "string")
          (eRel 0)
          [(pConstr "ReceiveContext_rocq" ["x0"; "x1"; "x2"], eRel 1)]))
    ; ("receiveSelfAddress", eLambda "x"
        (tyInd "ReceiveContext")
        (eCase
          ("ReceiveContext", [])
          (tyInd "nat")
          (eRel 0)
          [(pConstr "ReceiveContext_rocq" ["x0"; "x1"; "x2"], eRel 0)]))
    ].

  MetaRocq Run (translateData stdlib_prefixes ABl_data).

  MetaRocq Run (translateDefs stdlib_prefixes (StdLib.Σ ++ ABl_data)%list ABl_functions).
End AcornBlochain.

(** ** A simple [Counter] contract *)

(** Concrete syntax *)

(*
module RocqExamples where

import Prim

data Msg = Inc [Int64] | Dec [Int64]

data CState = CState [Int64, {address}]

definition owner (s :: CState) =
   case s of
     CState _ d -> d

definition balance (s :: CState) =
   case s of
     CState x _ -> x

definition count (s :: CState) (msg :: Msg) =
  case msg of
    Inc a ->
      CState (Prim.plusInt64 (balance s) a) (owner s)
    Dec a ->
      CState (Prim.minusInt64 (balance s) a) (owner s)
 *)

(** Data type definitions corresponding representation of the module [RocqExamples] above *)
Definition acorn_datatypes :=
  [ gdInd "Msg" 0
      [("Inc_rocq", [(None, tyInd "Z")]);
       ("Dec_rocq", [(None, tyInd "Z")])] false;
    gdInd "CState" 0
      [("CState_rocq", [(None, tyInd "Z");
       (None, tyInd "string")])] false].

MetaRocq Run (translateData [] acorn_datatypes).

Definition Σ' :=
  (StdLib.Σ ++ acorn_datatypes)%list.

(** For now, we assume that data types are already translated *)

Section Prim.
  Definition plusInt64 := Z.add.
  Definition minusInt64 := Z.sub.
End Prim.


(** Function definitions corresponding representation of the module [RocqExamples] above *)
Definition acorn_module : list (string * expr) :=
  [ ("owner", eLambda "x"
      (tyInd "CState")
      (eCase
        ("CState", [])
        (tyInd "string")
        (eRel 0)
        [(pConstr "CState_rocq" ["x0"; "x1"], eRel 0)]))
  ; ("balance", eLambda "x"
      (tyInd "CState")
      (eCase
        ("CState", [])
        (tyInd "Z")
        (eRel 0)
        [(pConstr "CState_rocq" ["x0"; "x1"], eRel 1)]))
  ; ("count", eLambda "x"
      (tyInd "CState")
      (eLambda "x"
        (tyInd "Msg")
        (eCase
          ("Msg", [])
          (tyInd "CState")
          (eRel 0)
          [(pConstr "Inc_rocq" ["x0"],
            eApp
              (eApp
                (eConstr "CState" "CState_rocq")
                (eApp
                  (eApp
                    (eConst "plusInt64")
                    (eApp (eConst "balance") (eRel 2)))
                  (eRel 0)))
              (eApp
                (eConst "owner")
                (eRel 2)));
           (pConstr "Dec_rocq" ["x0"],
            eApp
              (eApp
                (eConstr "CState" "CState_rocq")
                (eApp
                  (eApp
                    (eConst "minusInt64")
                    (eApp (eConst "balance") (eRel 2)))
                  (eRel 0)))
              (eApp (eConst "owner") (eRel 2)))])))
  ].

MetaRocq Run (translateDefs [] Σ' acorn_module).

Open Scope Z_scope.

Lemma inc_correct init_state n i final_state :
  (* precondition *)
  balance init_state = n ->

  (* sending "increment" *)
  count init_state (Inc_rocq i) = final_state ->

  (* result *)
  balance final_state = n + i.
Proof.
  intros Hinit Hrun. subst. reflexivity.
Qed.


Module ForPeresentation.

  (** This is how functions would look like, if we defined them by hand *)

Definition owner : CState -> string := fun x =>
  match x with
  | CState_rocq _ x1 => x1
  end.

Definition balance : CState -> Z := fun x =>
  match x with
  | CState_rocq x0 _ => x0
  end.

Definition count
  : CState -> Msg -> CState := fun x x0 =>
 match x0 with
 | Inc_rocq x1 =>
     CState_rocq (plusInt64 (balance x) x1)
                (owner x)
 | Dec_rocq x1 =>
   CState_rocq (minusInt64 (balance x) x1)
              (owner x)
 end.
End ForPeresentation.

Module Recursion.

  Definition R_data := [
    gdInd "Nat" 0 [("Zero_rocq", []); ("Suc_rocq", [(None, (tyInd "Nat"))])] false
  ].
  (*---------------------*)

  Open Scope nat.

  Definition R_functions :=
    [ ("add", eLetIn "f"
        (eFix "rec" "x"
          (tyInd "Nat")
          (tyArr (tyInd "Nat") (tyInd "Nat"))
          (eLambda "x"
            (tyInd "Nat")
            (eCase
              ("Nat", [])
              (tyInd "Nat")
              (eRel 1)
              [(pConstr "Zero_rocq" [], eRel 0);
               (pConstr "Suc_rocq" ["x0"],
                eApp
                  (eConstr "Nat" "Suc_rocq")
                  (eApp
                    (eApp (eRel 3) (eRel 0))
                    (eRel 1)))])))
        (tyArr
          (tyInd "Nat")
          (tyArr (tyInd "Nat") (tyInd "Nat")))
        (eRel 0))
    ].

  MetaRocq Run (translateData [] R_data).

  MetaRocq Run (translateDefs [] (StdLib.Σ ++ R_data)%list R_functions).

  Fixpoint Nat_nat (n : Nat) : nat :=
    match n with
    | Zero_rocq => O
    | Suc_rocq n' => S (Nat_nat n')
    end.

  Fixpoint nat_Nat (n : nat) : Nat :=
    match n with
    | O => Zero_rocq
    | S n' => Suc_rocq (nat_Nat n')
    end.

  Lemma Nat_nat_left n : nat_Nat (Nat_nat n) = n.
  Proof. induction n; simpl; f_equal; auto. Qed.


  Lemma Nat_nat_right n : Nat_nat (nat_Nat n) = n.
  Proof. induction n; simpl; f_equal; auto. Qed.

  #[local]
  Hint Resolve Nat_nat_left Nat_nat_right : hints.

  #[local]
  Set Warnings "-ambiguous-paths".

  #[local]
  Coercion Nat_nat : Nat >-> nat.
  #[local]
  Coercion nat_Nat : nat >-> Nat.

  Lemma add_correct (n m : Nat) :
  add n m = n + m.
  Proof. induction n; simpl; f_equal; auto with hints. Qed.

End Recursion.


(** Predicativity *)
Module Predicativity.
Definition id := fun (A : Set) (a : A) => a.

Definition id_id_syn :=
  eApp
    (eApp
      (eConst "id")
      (eTy (tyForall "A" (tyArr (tyRel 0) (tyRel 0)))))
    (eConst "id").

(* Eval compute in (expr_to_term StdLib.Σ (reindexify 0 id_id_syn)). *)

Definition id_forall :=
  eLambda "x"
    (tyForall "A" (tyArr (tyRel 0) (tyRel 0)))
    (eRel 0).

(* Compute (expr_to_term StdLib.Σ (reindexify 0 id_forall)). *)

(** Application [id id] fails, since [A] must be [Set], but type of
 [id] is [forall A, A -> A], which lives in [Type] *)
(* Compute (expr_to_tc StdLib.Σ (reindexify 0 id_id_syn)). *)
Fail MetaRocq Run (translateDefs [] [] [("id_id", id_id_syn)]).
(* Illegal application:
The term "id" of type "forall A : Set, A -> A"
cannot be applied to the terms
 "forall A : Set, A -> A" : "Type"
 "id" : "forall A : Set, A -> A"
The 1st term has type "Type" which should be coercible to
"Set".
 *)
End Predicativity.

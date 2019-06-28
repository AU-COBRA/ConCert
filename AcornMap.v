(* Implementing a simple finite map using our embedding *)
Require Import FMaps FMapWeakList.
Require Import String.
Require Import List.
Require Import PeanoNat.
Import ListNotations.
From Template Require Import All.

Require Import Ast CustomTactics.
Require Import EvalE.

Import MonadNotation.
Import BaseTypes.
Import StdLib.
Open Scope list.


Open Scope nat.

Fixpoint mkNames (ns : list string) (postfix : string) :=
  match ns with
  | [] => tmPrint "Done."
  | n :: ns' => n' <- tmEval all (n ++ postfix)%string ;;
                  str <- tmQuote n';;
                  tmMkDefinition n str;;
                  mkNames ns' postfix
  end.


Inductive AMaybe (A : Set) :=
| ANothing | AJust : A -> AMaybe A.

Inductive AMap (A B : Set) :=
| ANil : AMap A B | ACons : A -> B -> AMap A B -> AMap A B.

Definition Σ' :=
  Σ ++
    [gdInd "AMaybe" 2 [("ANothing", []);  ("AJust", [(nAnon,tyRel 0)])] false;
       gdInd "AMap" 2 [("ANil", []);  ("ACons", [(nAnon,tyRel 1);(nAnon,tyRel 0);
                                                   (nAnon,(tyApp (tyApp (tyInd "AMap") (tyRel 1)) (tyRel 0)))])] false ].


Definition Maybe := "AMaybe".
Definition Map := "AMap".
Definition MNil := "ANil".
Definition MCons := "ACons".

Run TemplateProgram
      (mkNames ["A"; "B"; "C"; "f"; "a"; "b"; "c"; "m"; "n"; "k" ; "v"; "lookup"; "add" ] "_coq").

Notation "'Nothing'" := (pConstr "ANothing" [])
                      (in custom pat at level 0).

Notation "'Nothing'" := (eConstr "AMaybe" "ANothing")
                      (in custom expr at level 0).

Notation "'Just'" := (eConstr "AMaybe" "AJust")
                      (in custom expr at level 0).


Notation "'MNil'" := (pConstr MNil [])
                      (in custom pat at level 0).

Notation "'MCons' x y z" := (pConstr MCons [x;y;z])
                    (in custom pat at level 0,
                        x constr at level 4,
                        y constr at level 4,
                        z constr at level 4).

Notation "'MNil'" := (eConstr "AMap" "ANil")
                      (in custom expr at level 0).

Notation "'MCons'" := (eConstr "AMap" "ACons")
                        (in custom expr at level 0).

Notation " ' x " := (eTy (tyVar x))
                    (in custom expr at level 1,
                        x constr at level 2).

Notation "'if' cond 'then' b1 'else' b2 : ty" :=
    (eCase (tyInd Bool,0) ty cond
           [(pConstr true_name [],b1);(pConstr false_name [],b2)])
      (in custom expr at level 2,
          cond custom expr at level 4,
          ty custom type at level 4,
          b1 custom expr at level 4,
          b2 custom expr at level 4).


Definition lookup_syn :=
  [| \\A => \\B =>
     \f : 'A -> 'A -> Bool =>
     \k : 'A =>
     fix lookup (m : Map 'A 'B) : Maybe 'B :=
     case m : Map 'A 'B # 2 return Maybe 'B of
     | MNil -> Nothing 'B
     | MCons x y z -> if (f k x) then
                       Just 'B y
                       else lookup z : Maybe 'B |].

Definition lookup_syn' :=
  [| \\A => \\B =>
     \f : 'A -> 'A -> Bool =>
     \k : 'A =>
     \v : 'B =>
     fix lookup (m : Map 'A 'B) : Maybe 'B :=
     case (MNil 'A 'B) : Map 'A 'B # 2 return Maybe 'B of
     | MNil -> Nothing 'B
     | MCons x y z -> if (f k x) then
                       Just 'B y
                       else lookup z : Maybe 'B |].


Make Definition lookup_map := Eval compute in (expr_to_term Σ' (indexify [] lookup_syn)).


Definition add_map_syn :=
    [| \\A => \\B =>
     \f : 'A -> 'A -> Bool =>
     \k : 'A =>
     \v : 'B =>
     fix add (m : Map 'A 'B) : Map 'A 'B :=
     case m : Map 'A 'B # 2 return Map 'A 'B of
     | MNil -> MCons 'A 'B k v (MNil 'A 'B)
     | MCons x y z -> if (f k x) then
                       MCons 'A 'B k v z
                     else MCons 'A 'B x y (add z) : Map 'A 'B |].

Make Definition add_map := Eval compute in (expr_to_term Σ' (indexify [] add_map_syn)).

Module NatMap := FMapWeakList.Make Nat_as_OT.

Fixpoint from_amap {A} (m : AMap nat A) : NatMap.Raw.t A :=
  match m with
  | ANil _ _ => []
  | ACons _ _ k v m' => (k,v) :: from_amap m'
  end.

Import PeanoNat.Nat.

(* Showing that Acorn maps are the same as one of the Stdlib implementations
   (we fix keys to be natural numbers) *)
Lemma add_map_eq_stdlib {A : Set} k v m :
  NatMap.Raw.add k v (from_amap m) = from_amap (add_map _ A PeanoNat.Nat.eqb k v m).
Proof.
  induction m.
  + reflexivity.
  + simpl in *.
    destruct (Nat_as_OT.eq_dec k a0). subst. rewrite eqb_refl.
    reflexivity. rewrite <- eqb_neq in n0. rewrite n0.
    simpl. now f_equal.
Qed.


Module MapEval.

  (* Computing with the interpreter *)

  Import InterpreterEnvList.

  Definition tyNat := eTy (tyInd Nat).

  (* A simple example first *)

  Definition case_ex1 :=
    [| \\y  => \"w" : 'y => \x : 'y =>  \z : "list" 'y =>
           case z : "list" 'y # 1 return "prod" 'y 'y of
           | Nil -> {eConstr "prod" "Pair"} {eTy (tyVar y)} {eTy (tyVar y)} x "w"
           | Cons "hd" "tl" -> {eConstr "prod" "Pair"} {eTy (tyVar y)} {eTy (tyVar y)} "hd" x |].

  Make Definition case_ex_def1 := Eval compute in (expr_to_term Σ' (indexify [] case_ex1)).

  Compute (expr_eval_n 20 Σ' [] ([| {case_ex1} {tyNat} 0 1 ({eConstr "list" "Nil"} {tyNat}) |])).

  Definition eqb_syn :=
    [| (fix "eqb" (n : Nat) : Nat ->  Bool :=
           case n : Nat return Nat -> Bool of
           | Z -> \m : Nat => (case m : Nat return Bool of
                   | Z -> True
                   | Suc z -> False)
           | Suc a ->
             \m : Nat =>
             (case m : Nat return Bool of
                   | Z -> False
                   | Suc b -> "eqb" a b))
     |].

  Make Definition nat_eqb := Eval compute in (expr_to_term Σ' (indexify [] eqb_syn)).

  Lemma nat_eqb_correct n m : nat_eqb n m = Nat.eqb n m.
  Proof.
    revert m.
    induction n;intros m; now destruct m.
  Qed.

  Definition aMap := [| MCons {tyNat} {tyNat} 1 1 (MCons {tyNat} {tyNat} 0 0 (MNil {tyNat} {tyNat})) |].

  Compute resolve_constr Σ' "AMap" "ACons".
  Compute (expr_eval_i 20 Σ' []
                       (indexify [] [|  {eqb_syn} 1 1 |])).
  Compute (expr_eval_i 20 Σ' []
                       (indexify [] [|  {aMap} |])).

  Compute (expr_eval_n 20 Σ' [] ([| {lookup_syn} {tyNat} {tyNat} {eqb_syn} 0 {aMap} |])).

  Compute (expr_eval_i 20 Σ' [] (indexify [] [| {lookup_syn} {tyNat} {tyNat} {eqb_syn} 0 {aMap} |])).

  Compute (expr_eval_i 20 Σ' []
                       (indexify [] [| {add_map_syn} {tyNat} {tyNat} {eqb_syn} 0 1 (MNil {tyNat} {tyNat}) |])).

  Definition zzz := [| \\A => \x : ∀ B, 'B -> 'A => x |].

  Make Definition zzzzz := Eval compute in (expr_to_term Σ' (indexify [] zzz)).

  Compute (expr_eval_i 20 Σ' []
                       (indexify [] [| {zzz} {tyNat} (\\B => \x :'B => 0)|])).

  End MapEval.
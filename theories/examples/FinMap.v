(** * Implementing a simple finite map using our embedding *)
Require Import FMaps FMapWeakList.
Require Import String Basics.
Require Import List.
Require Import PeanoNat.
Import ListNotations.
From MetaCoq.Template Require Import All.

From ConCert Require Import Ast Notations CustomTactics PCUICTranslate PCUICtoTemplate EvalE.

Import MonadNotation.
Import BaseTypes.
Import StdLib.
Open Scope list.
Open Scope nat.

Definition expr_to_tc Σ := compose trans (expr_to_term Σ).
Definition type_to_tc := compose trans type_to_term.
Definition global_to_tc := compose trans_minductive_entry trans_global_dec.


(** Generation of string constants using MetaCoq *)

Fixpoint mkNames (ns : list string) (postfix : string) :=
  match ns with
  | [] => tmPrint "Done."
  | n :: ns' => n' <- tmEval all (n ++ postfix)%string ;;
                  str <- tmQuote n';;
                  tmMkDefinition n str;;
                  mkNames ns' postfix
  end.

(** ** The deep embedding of data structures for finite maps *)

(** We generate names for inductives and constructors *)
Run TemplateProgram
      (mkNames ["Maybe";"Nothing";"Just"; "Map"; "MNil"; "MCons" ] "Oak").

(** [AMaybe] is similar to [option] of Coq and [Maybe] of Haskell. *)

Definition maybe_syn :=
  gdInd Maybe 1 [(Nothing, []);  (Just, [(None,tyRel 0)])] false.

Make Inductive (global_to_tc maybe_syn).

(** A finite map is basically a list of pairs *)
Definition map_syn :=
  gdInd Map 2
        [(MNil, []);
        (MCons, [(None,tyRel 1);(None,tyRel 0);
                  (None,(tyApp (tyApp (tyInd Map) (tyRel 1)) (tyRel 0)))])] false.

Make Inductive (global_to_tc map_syn).

Definition Σ' :=
  Σ ++ [ maybe_syn; map_syn ].

(** We generate string constants for variable names to make our examples look nicer *)
Run TemplateProgram
      (mkNames ["A"; "B"; "C"; "f"; "a"; "b"; "c"; "m"; "n"; "k" ; "v"; "w"; "x"; "y"; "z"; "lookup"; "add" ] "_coq").

(** A bit of additional notations required for patterns and constructors *)

Notation "'Nothing'" := (pConstr Nothing [])
                      (in custom pat at level 0).

Notation "'Nothing'" := (eConstr Maybe "NothingOak")
                      (in custom expr at level 0).

Notation "'Just'" := (eConstr Maybe Just)
                      (in custom expr at level 0).


Notation "'MNil'" := (pConstr MNil [])
                      (in custom pat at level 0).

Notation "'MCons' x y z" := (pConstr MCons [x;y;z])
                    (in custom pat at level 0,
                        x constr at level 4,
                        y constr at level 4,
                        z constr at level 4).

Notation "'MNil'" := (eConstr Map "MNilOak")
                      (in custom expr at level 0).

Notation "'MCons'" := (eConstr Map "MConsOak")
                        (in custom expr at level 0).

Notation " ' x " := (eTy (tyVar x))
                    (in custom expr at level 1,
                        x constr at level 2).

(** [if .. then .. else] is just a shortcut for [case] of a boolean expression *)
Notation "'if' cond 'then' b1 'else' b2 : ty" :=
    (eCase (Bool,[]) ty cond
           [(pConstr true_name [],b1);(pConstr false_name [],b2)])
      (in custom expr at level 2,
          cond custom expr at level 4,
          ty custom type at level 4,
          b1 custom expr at level 4,
          b2 custom expr at level 4).

(** ** Functions on finite maps *)

(** AST for lookup function *)
Definition lookup_syn :=
  [| \\A => \\B =>
     \f : 'A -> 'A -> Bool =>
     \k : 'A =>
     fix lookup (m : Map 'A 'B) : Maybe 'B :=
     case m : Map 'A ,'B return Maybe 'B of
     | MNil -> Nothing 'B
     | MCons x y z -> if (f k x) then
                       Just 'B y
                       else lookup z : Maybe 'B |].

Compute (indexify [] lookup_syn).
(** Unquoting the [lookup_syn] to produce a Coq function *)
Make Definition lookup_map := (expr_to_tc Σ' (indexify [] lookup_syn)).

(** AST for a function that adds an element to a map *)
Definition add_map_syn :=
    [| \\A => \\B =>
     \f : 'A -> 'A -> Bool =>
     \k : 'A =>
     \v : 'B =>
     fix add (m : Map 'A 'B) : Map 'A 'B :=
     case m : Map 'A , 'B return Map 'A 'B of
     | MNil -> MCons 'A 'B k v (MNil 'A 'B)
     | MCons x y z -> if (f k x) then
                       MCons 'A 'B k v z
                     else MCons 'A 'B x y (add z) : Map 'A 'B |].

Compute (expr_to_term Σ' (indexify [] add_map_syn)).

Make Definition add_map := (expr_to_tc Σ' (indexify [] add_map_syn)).

(** ** Correctness *)

(** We can prove correctness of "library" definitions like finite maps by comparing the to Coq's standard library definitions *)

(** Since Coq's [FMap] is a module, we fix the type of keys to be [nat] *)
Module NatMap := FMapWeakList.Make Nat_as_OT.

(** Conversion function from our type of finite maps to the one in the standard library *)
Fixpoint from_amap {A} (m : MapOak nat A) : NatMap.Raw.t A :=
  match m with
  | MNilOak  => []
  | MConsOak k v m' => (k,v) :: from_amap m'
  end.

Import PeanoNat.Nat.

(** Showing that Oak finite maps are the same as one of the Stdlib implementations (up to converting the results) *)
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

(** * Computing with the interpreter *)

Section MapEval.

  Definition tyNat := eTy (tyInd Nat).

  (** Boolean equality of two natural numbers in Oak *)
  Definition eqb_syn : expr :=
    [| (fix "eqb" (n : Nat) : Nat ->  Bool :=
           case n : Nat return Nat -> Bool of
           | Zero -> \m : Nat => (case m : Nat return Bool of
                   | Zero -> True
                   | Suc z -> False)
           | Suc a ->
             \m : Nat =>
             (case m : Nat return Bool of
                   | Zero -> False
                   | Suc b -> "eqb" a b))
     |].

  Make Definition nat_eqb :=
    (expr_to_tc Σ' (indexify [] eqb_syn)).

  (** Showing that Oak boolean equality is in fact the same as [Nat.eqb] *)
  Lemma nat_eqb_correct n m : nat_eqb n m = Nat.eqb n m.
  Proof.
    revert m.
    induction n;intros m; now destruct m.
  Qed.

  (** The syntactic representation of the following map [1 ~> 1; 0 ~> 0] *)
  Definition aMap :=
    [| MCons {tyNat} {tyNat} 1 1 (MCons {tyNat} {tyNat} 0 0 (MNil {tyNat} {tyNat})) |].

  (** Computing boolean equality with the interpreter *)
  Example compute_eqb_true :
    (expr_eval_i Σ' 10 [] (indexify [] [|{eqb_syn} 1 1 |])) =
    Ok (vConstr Bool true_name []).
  Proof. reflexivity. Qed.

  Example compute_eqb_false :
    (expr_eval_i Σ' 10 [] (indexify [] [|{eqb_syn} 1 0 |])) =
    Ok (vConstr Bool false_name []).
  Proof. reflexivity. Qed.


  (** Computing lookup with using the interpreter for the named representation of variables *)
  Example compute_lookup_named :
    (expr_eval_n Σ' 10 []
                 [| {lookup_syn} {tyNat} {tyNat} {eqb_syn} 0 {aMap} |]) =
  Ok (vConstr Maybe "JustOak" [vTy (tyInd Nat); vConstr Nat "Z" []]).
  Proof. compute. reflexivity. Qed.


  (** Computing lookup with using the interpreter for variables represented with De Bruijn indices *)
  Example compute_lookup_debruijn :
    (expr_eval_i Σ' 10 []
                 (indexify []
                           [| {lookup_syn} {tyNat} {tyNat} {eqb_syn} 0 {aMap} |])) =
  Ok (vConstr Maybe "JustOak" [vTy (tyInd Nat); vConstr Nat "Z" []]).
  Proof. compute. reflexivity. Qed.

End MapEval.
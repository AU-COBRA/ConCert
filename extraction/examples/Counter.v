From Coq Require Import List String ZArith.
From ConCert.Embedding Require Import Utils Notations Ast MyEnv.
From ConCert.Extraction Require Import Liquidity.
From ConCert.Extraction Require Import SimpleBlockchain Prelude.

Import ListNotations.

Module Counter.
  Import AcornBlockchain.
  (** Generating names for the data structures  *)
  Run TemplateProgram
       (mkNames ["n"; "own"; "st" ; "new_st" ; "new_balance" ; "state" ; "MkState" ; "owner" ; "msg" ; "Inc" ; "Dec"; "addr" ] "_coq").

  (** ** Definitions of data structures for the contract *)

  (** The contract's state. We use the product type directly, because records are not yet supported by extraction *)
  (* TODO: make address a separate data type (say, a wrapper around nat) to be able to recognise it in the extraction *)
  Notation "'CounterState'" := [! money × address !] (in custom type).

  Notation "'balance' a" :=
    [| first money address {a} |]
      (in custom expr at level 0).

  Notation "'owner' a" :=
    [| second money address {a} |]
      (in custom expr at level 0).

  Definition update_balance_syn :=
    [| \st : money × address => \new_balance : money =>
       Pair money address (balance st + new_balance) (owner st) |].

  Notation "'update_balance' a b" :=
    [| {eConst "_update_balance"} {a} {b} |]
      (in custom expr at level 0,
          a custom expr at level 1,
          b custom expr at level 1).


  (** Messages *)
  Definition msg_syn :=
  [\ data msg =
       Inc [money,_]
     | Dec [money,_] \].

  (** The main functionality *)
  Definition counter_syn :=
    [| \msg : msg => \st : CounterState =>
       case msg : msg return Maybe ((List "SimpleActionBody") ×  CounterState) of
         | Inc n -> $Just$Maybe [: List "SimpleActionBody" × CounterState]
                        (Pair (List "SimpleActionBody") CounterState
                              (Nil "SimpleActionBody")
                              (update_balance st n))
         | Dec n -> $Nothing$Maybe [: List "SimpleActionBody" × CounterState] |].

  (** Packing together the data type definitions and functions *)
  Definition CounterModule : LiquidityModule :=
    {| datatypes := [msg_syn];
       storage := [! CounterState !];
       init := [| \n : money => \addr : address => Pair money address n addr  |];
       message := [! msg !];
       functions := [("_update_balance", update_balance_syn);
                       ("counter", counter_syn)];
       main := "counter";
       main_extra_args := []|}.

  Definition Σ' :=
    (Prelude.Σ ++ [ Prelude.AcornMaybe; msg_syn])%list.

  Make Inductive (global_to_tc msg_syn).

  Make Definition _update_balance :=
    (expr_to_tc Σ' (indexify nil update_balance_syn)).

  Make Definition counter :=
    (expr_to_tc Σ' (indexify nil counter_syn)).

End Counter.

(** A translation table for types*)
Definition TTty : env string :=
  [("address_coq", "address");
     ("Coq.Numbers.BinNums.Z", "tez");
     ("Coq.Init.Datatypes.nat", "nat")].

(** A translation table for primitive binary operations *)
Definition TT : env string :=
  [("Coq.ZArith.BinInt.Z.add", "addTez")].

Compute liquidify TT TTty
        ([| {eConstr "prod" "pair"} {eTy (tyInd "A")} {eTy (tyInd "B")} "b" "o" |]).

(** The output has been tested in the online Liquidity editor: https://www.liquidity-lang.org/edit/ *)
Compute liquidifyModule TT TTty Counter.CounterModule.

(** An attempt of extraction from the shallow embedding using the "native" Coq extraction mechanism *)

Extraction Language OCaml.

Extract Inductive list => "list" [ "[]" "(::)" ].
Extract Inductive prod => "(*)"  [ "(,)" ].
Extract Inductive Z => "tez" ["0DUN" "id" "negate"].
Extract Inlined Constant Z.add => "addTez".

(** In Liquidify, [+] is overloaded and thus requires type annotations. We can overcome this issue by un-overloading the operations and providing specialised versions (not infix anymore). *)

(** Essentially, we need to prepend the follwing "prelude" before our contracts: *)
(** let[@inline] fst (p : 'a * 'b) : 'a = p.(0)
    let[@inline] snd (p : 'a * 'b) : 'b = p.(1)
    let[@inline] addN (n : nat) (m : nat) = n + m
    let[@inline] addTez (n : tez) (m : tez) = n + m *)

(** It seems there are some syntactic and semantic differences from OCaml. E.g. it's not possible to pattern-match on tuples in Liquidity, a special form of [let] or projections must be used instead. That's why our "prelude" features the [fst] and [snd] functions. We use them explicitly instead of destructing pairs. *)

Extraction Counter._update_balance.
Extraction Counter.counter.

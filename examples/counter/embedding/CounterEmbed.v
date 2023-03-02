From Coq Require Import List.
From Coq Require Import String.
From Coq Require Import ZArith.
From ConCert.Embedding Require Import Utils.
From ConCert.Embedding Require Import Notations.
From ConCert.Embedding Require Import Ast.
From ConCert.Embedding Require Import PCUICTranslate.
From ConCert.Embedding Require Import TranslationUtils.
From ConCert.Embedding Require Import SimpleBlockchain.
From ConCert.Embedding Require Import Prelude.
From ConCert.Embedding.Extraction Require Import Liquidity.
From ConCert.Embedding.Extraction Require Import PreludeExt.
From ConCert.Utils Require Import Env.
From MetaCoq.Template Require Import All.
Import ListNotations.
Import MCMonadNotation.

Module Counter.
  Import AcornBlockchain.

  Open Scope list.

  (** Generating names for the data structures *)
  MetaCoq Run
          (mp_ <- tmCurrentModPath tt ;;
           let mp := (PCUICTranslate.string_of_modpath mp_ ++ "@")%string in
            mkNames mp ["state"; "MkState"; "owner"; "msg" ] "_coq").

  (** Variable names and constructor names *)
  MetaCoq Run (mkNames "" ["m"; "n"; "own"; "st" ; "new_st" ; "addr" ; "new_balance"; "Inc" ; "Dec"] "_coq").

  (** ** Definitions of data structures for the contract *)

  (** The contract's state. We use the product type directly, because records are not yet supported by extraction *)
  (* TODO: make address a separate data type (say, a wrapper around nat) to be able to recognize it in the extraction *)
  Notation "'CounterState'" := [! money × address !] (in custom type).

  Notation "'balance' a" :=
    [| first money address {a} |]
      (in custom expr at level 0).

  Notation "'owner' a" :=
    [| second money address {a} |]
      (in custom expr at level 0).

  (** Messages *)
  Definition msg_syn :=
  [\ data msg =
       Inc [money,_]
     | Dec [money,_] \].

  Definition Σ' :=
    (StdLib.Σ ++ [ Prelude.AcornMaybe; msg_syn])%list.

    Definition update_balance_syn :=
    [| \st : money × address => \new_balance : money =>
       Pair money address (balance st + new_balance) (owner st) |].

  MetaCoq Unquote Definition _update_balance :=
    (expr_to_tc Σ' (indexify nil update_balance_syn)).


  Notation "'update_balance' a b" :=
    [| {eConst (to_string_name <% _update_balance %>)} {a} {b} |]
      (in custom expr at level 0,
          a custom expr at level 1,
          b custom expr at level 1).

  (** The main functionality *)
  Definition counter_syn :=
    [| \m : msg => \st : CounterState =>
       case m : msg return Maybe ((List SimpleActionBody) × CounterState) of
         | Inc n -> $Just$Maybe [: List SimpleActionBody × CounterState]
                        (Pair (List SimpleActionBody) CounterState
                              (Nil SimpleActionBody)
                              (update_balance st n))
         | Dec n -> $Nothing$Maybe [: List SimpleActionBody × CounterState] |].

  (** Packing together the data type definitions and functions *)
  Definition CounterModule : LiquidityModule :=
    {| datatypes := [msg_syn];
       storage := [! CounterState !];
       init := [| \n : money => \addr : address => \"c" : CallCtx =>
                  $Just$Maybe [: money × address] Pair money address n addr |];
       message := [! msg !];
       functions := [("_update_balance", update_balance_syn);
                       ("counter", counter_syn)];
       main := "counter";
       main_extra_args := []|}.

  MetaCoq Unquote Inductive (global_to_tc msg_syn).

  MetaCoq Unquote Definition counter :=
    (expr_to_tc Σ' (indexify nil counter_syn)).

End Counter.

(** A translation table for types*)
Definition TTty :=
  [(to_string_name <% address_coq %>, "address");
   (to_string_name <% time_coq %>, "timestamp");
   (to_string_name <% Z %>, "tez");
   (to_string_name <% nat %>, "nat")].

(** A translation table for primitive binary operations *)
Definition TT :=
  [(to_string_name <% Z.add %>, "addTez")].

(** The output has been tested in the online Liquidity editor: https://www.liquidity-lang.org/edit/ *)
(* Compute liquidifyModule TT TTty Counter.CounterModule. *)

(** An attempt of extraction from the shallow embedding using the "native" Coq extraction mechanism *)

Extraction Language OCaml.

Extract Inductive list => "list" [ "[]" "(::)" ].
Extract Inductive prod => "(*)" [ "(,)" ].
Extract Inductive Z => "tez" ["0DUN" "id" "negate"].
Extract Inlined Constant Z.add => "addTez".

(** In Liquidify, [+] is overloaded and thus requires type annotations. We can overcome this issue by un-overloading the operations and providing specialized versions (not infix anymore). *)

(** Essentially, we need to prepend the follwing "prelude" before our contracts: *)
(** let[@inline] fst (p : 'a * 'b) : 'a = p.(0)
    let[@inline] snd (p : 'a * 'b) : 'b = p.(1)
    let[@inline] addN (n : nat) (m : nat) = n + m
    let[@inline] addTez (n : tez) (m : tez) = n + m *)

(** It seems there are some syntactic and semantic differences from OCaml. E.g. it's not possible to pattern-match on tuples in Liquidity, a special form of [let] or projections must be used instead. That's why our "prelude" features the [fst] and [snd] functions. We use them explicitly instead of destructing pairs. *)

(* Extraction Counter._update_balance. *)
(* Extraction Counter.counter. *)

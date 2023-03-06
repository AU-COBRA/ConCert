(** * Data types for the crowdfunding contract *)

From Coq Require Import String.
From Coq Require Import List.
From ConCert.Embedding Require Import Ast.
From ConCert.Embedding Require Import Notations.
From ConCert.Embedding Require Import PCUICTranslate.
From ConCert.Embedding Require Import SimpleBlockchain.
From ConCert.Embedding Require Import Utils.
From ConCert.Embedding Require Import TranslationUtils.
From ConCert.Embedding Require Import Prelude.

Import ListNotations.
From MetaCoq.Template Require Import All.

Import MCMonadNotation.
Import BaseTypes.
Open Scope list.

Import AcornBlockchain Prelude.Maps.
Set Nonrecursive Elimination Schemes.

(** Note that we define the deep embedding (abstract syntax trees) of the data structures and programs using notations. These notations are defined in [Ast.v] and make use of the "custom entries" feature. *)

(** Brackets like [[\ \]] delimit the scope of data type definitions and like [[| |]] the scope of programs *)

(** Generating names for the data structures. We also add a prefix, corresponding ti the current module path. *)
MetaCoq Run
        ( mp_ <- tmCurrentModPath tt ;;
          let mp := (PCUICTranslate.string_of_modpath mp_ ++ "@")%string in
          mkNames mp
             ["State" ; "mkState"; "balance" ; "donations" ; "owner";
              "deadline"; "goal"; "done";
              "Res" ; "Error";
              "Msg"; "Donate"; "GetFunds"; "Claim";
              "Action"; "Transfer"; "Empty" ] "_coq").

Import ListNotations.

(** ** Definitions of data structures for the contract *)

(** The internal state of the contract *)
Definition state_syn : global_dec :=
  [\ record State :=
     mkState { balance : Money ;
       donations : Map;
       owner : Address;
       deadline : Nat;
       done : Bool;
       goal : Money } \].

(* TODO: MetaCoq does not generate projections at the moment.
     (However, it worked before somehow)
     Probably related to https://github.com/MetaCoq/metacoq/issues/369

     For now, we just define records explicitly.
   *)

Record State_coq : Set := mkState_coq
  { balance_coq : BinNums.Z;
    donations_coq : addr_map_coq;
    owner_coq : nat;
    deadline_coq : nat;
    done_coq : bool;
    goal_coq : BinNums.Z }.

(** We can print actual AST by switching off the notations *)

Unset Printing Notations.

(* state_syn =
    gdInd State O
      (cons
         (rec_constr State
            (cons (pair (nNamed balance) (tyInd Money))
               (cons (pair (nNamed donations) (tyInd Map))
                  (cons (pair (nNamed owner) (tyInd Money))
                     (cons (pair (nNamed deadline) (tyInd Nat))
                        (cons (pair (nNamed goal) (tyInd Money)) nil)))))) nil) true
         : global_dec *)

Set Printing Notations.

(** Unquoting the definition of a record *)

(* FIXME: disabled due to the issue with generating projections *)
(* MetaCoq Unquote Inductive (global_to_tc state_syn). *)

(** As a result, we get a new Coq record [State_coq] *)

Definition msg_syn :=
  [\ data Msg =
       Donate [_]
     | GetFunds [_]
     | Claim [_] \].

MetaCoq Unquote Inductive (global_to_tc msg_syn).

(** Custom notations for patterns, projections and constructors *)
Module Notations.

  Notation "'ctx_from' a" := [| {eConst (to_string_name <% Ctx_from %>)} {a} |]
                             (in custom expr at level 0).
  Notation "'ctx_contract_address' a" :=
    [| {eConst (to_string_name <% Ctx_contract_address %>)} {a} |]
      (in custom expr at level 0).
  Notation "'amount' a" := [| {eConst (to_string_name <% Ctx_amount %>)} {a} |]
                             (in custom expr at level 0).


  (** Projections *)
  Notation "'balance' a" :=
    [| {eConst balance} {a} |]
      (in custom expr at level 0).
  Notation "'donations' a" :=
    [| {eConst donations} {a} |]
      (in custom expr at level 0).
  Notation "'owner' a" :=
    [| {eConst owner} {a} |]
      (in custom expr at level 0).
  Notation "'deadline' a" :=
    [| {eConst deadline} {a} |]
      (in custom expr at level 0).
  Notation "'goal' a" :=
    [| {eConst goal} {a} |]
      (in custom expr at level 0).
  Notation "'done' a" :=
    [| {eConst done} {a} |]
      (in custom expr at level 0).


  Notation "'Nil'" := [| {eConstr List "nil"} {eTy (tyInd SActionBody)} |]
                      (in custom expr at level 0).

  Notation " x ::: xs" := [| {eConstr List "cons"} {eTy (tyInd SActionBody)} {x} {xs} |]
                            ( in custom expr at level 0).

  Notation "[ x ]" := [| {eConstr List "cons"} {eTy (tyInd SActionBody)} {x} Nil |]
                        ( in custom expr at level 0,
                          x custom expr at level 1).
  (** Constructors. [Res] is an abbreviation for [Some (st, [action]) : option (State * list ActionBody)] *)

  Definition actions_ty := [! List SActionBody !].

  Notation "'Result'" := [! Prod State (List SActionBody) !]
                           (in custom type at level 2).


  Definition mk_res a b := [| {eConstr "option" "Some"}
                                {eTy [! Result !]}
                                 ({eConstr Prod "pair"} {eTy (tyInd State)}
                                 {eTy actions_ty} {a} {b}) |].
  Notation "'Res' a b" := (mk_res a b)
      (in custom expr at level 2,
          a custom expr at level 4,
          b custom expr at level 4).

  Notation "'mkState' a b" :=
    [| {eConstr State mkState} {a} {b} |]
      (in custom expr at level 0,
          a custom expr at level 1,
          b custom expr at level 1).

  Notation "'Transfer' a b" :=
    [| {eConstr SActionBody "Act_transfer"} {b} {a} |]
      (in custom expr at level 0,
          a custom expr at level 1,
          b custom expr at level 1).

  Notation "'Empty'" := (eConstr Action Empty)
                      (in custom expr at level 0).

  (** New global context with the constants defined above (in addition to the ones defined in the Oak's "StdLib") *)

  Import Maps.

  Definition Σ' :=
    (StdLib.Σ ++ [ Prelude.AcornMaybe;
           state_syn;
           msg_syn;
           addr_map_acorn;
           AcornBlockchain.SimpleChainAcorn;
           AcornBlockchain.SimpleContractCallContextAcorn;
           AcornBlockchain.SimpleActionBodyAcorn;
           gdInd "Z" 0 [("Z0", []); ("Zpos", [(None,tyInd "positive")]);
                          ("Zneg", [(None,tyInd "positive")])] false])%list.

  End Notations.


Import Prelude.

(** Generating string constants for variable names *)

MetaCoq Run (mkNames "" ["c"; "s"; "e"; "m"; "v"; "dl"; "g"; "chain";
                     "tx_amount"; "bal"; "sender"; "own"; "isdone" ;
                     "accs"; "now";
                     "newstate"; "newmap"; "cond"] "").

(** A shortcut for [if .. then .. else ..] *)
Notation "'if' cond 'then' b1 'else' b2 : ty" :=
  (eCase (Bool,[]) ty cond
         [(pConstr true_name [],b1); (pConstr false_name [],b2)])
    (in custom expr at level 4,
        cond custom expr at level 4,
        ty custom type at level 4,
        b1 custom expr at level 4,
        b2 custom expr at level 4).

Definition SCtx := to_string_name <% SimpleContractCallContext_coq %>.

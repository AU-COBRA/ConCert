(** * Data types for the crowdfunding contract *)

Require Import String ZArith Basics.
From ConCert Require Import Ast Notations PCUICTranslate.
From ConCert Require Import Utils Prelude CounterBlockchain.
Require Import List PeanoNat ssrbool.

Import ListNotations.
From MetaCoq.Template Require Import All.

Import MonadNotation.
Import BaseTypes.
Open Scope list.


Import CounterBlockchain.

(** Note that we define the deep embedding (abstract syntax trees) of the data structures and programs using notations. These notations are defined in  [Ast.v] and make use of the "custom entries" feature. *)

(** Brackets like [[\ \]] delimit the scope of data type definitions and like [[| |]] the scope of programs *)

Run TemplateProgram
      (mkNames ["State" ; "mkState";
                "counter"; "blob";
                "Res" ; "Error";
                "Msg"; "Incr";
                "Action"; "Transfer"; "Empty" ] "_coq").
Import ListNotations.


(** ** Definitions of data structures for the contract *)

(** The internal state of the contract *)
Definition state_syn : global_dec :=
  [\ record State :=
     mkState {counter : CounterValue; blob: CounterValue} \].

(** We can print actual AST by switching off the notations *)

Unset Printing Notations.

Print state_syn.

Set Printing Notations.

(** Unquoting the definition of a record *)
Set Nonrecursive Elimination Schemes.
Make Inductive (global_to_tc state_syn).

(** As a result, we get a new Coq record [State_coq] *)
Print State_coq.

Definition msg_syn :=
  [\ data Msg =
       Incr [_]
      \].

Make Inductive (global_to_tc msg_syn).

(** Custom notations for patterns, projections and constructors *)
Module Notations.

  Notation "'ctx_from' a" := [| {eConst "Ctx_from"} {a} |]
                             (in custom expr at level 0).
  Notation "'ctx_contract_address' a" :=
    [| {eConst "Ctx_contract_address"} {a} |]
      (in custom expr at level 0).
  Notation "'amount' a" := [| {eConst "Ctx_amount"} {a} |]
                             (in custom expr at level 0).


  (** Patterns *)
  Notation "'Incr'" :=
    (pConstr Incr []) (in custom pat at level 0).
  
  Notation "'Just' x" :=
    (pConstr "Some" [x]) (in custom pat at level 0,
                             x constr at level 4).
  Notation "'Nothing'" := (pConstr "None" [])
                            (in custom pat at level 0).

  (** Projections *)
  Notation "'counter' a" :=
    [| {eConst counter} {a} |]
      (in custom expr at level 0).
  Notation "'blob' a" :=
    [| {eConst blob} {a} |]
      (in custom expr at level 0).


  Notation "'Nil'" := [| {eConstr "list" "nil"} {eTy (tyInd CActionBody)} |]
                      (in custom expr at level 0).

  Notation " x ::: xs" := [| {eConstr "list" "cons"} {eTy (tyInd CActionBody)} {x} {xs} |]
                            ( in custom expr at level 0).

  Notation "[ x ]" := [| {eConstr "list" "cons"} {eTy (tyInd CActionBody)} {x} Nil |]
                        ( in custom expr at level 0,
                          x custom expr at level 1).
  (** Constructors. [Res] is an abbreviation for [Some (st, [action]) : option (State * list ActionBody)] *)



  Definition actions_ty := [! "list" "CounterActionBody" !].

  Notation "'Result'" := [!"prod" State ("list" "CounterActionBody") !]
                           (in custom type at level 2).

  Notation "'Just' a" := [| {eConstr "option" "Some"}  {eTy [! Result!]} {a}|]
                           (in custom expr at level 0,
                               a custom expr at level 1).

  Notation "'Pair' a b" := [| {eConstr "prod" "pair"}
                               {eTy (tyInd State)}
                               {eTy actions_ty} {a} {b} |]
                           (in custom expr at level 0,
                               a custom expr at level 1,
                               b custom expr at level 1).


  Definition mk_res a b := [| {eConstr "option" "Some"}
                                {eTy [! Result !]}
                                 ({eConstr "prod" "pair"} {eTy (tyInd State)}
                                 {eTy actions_ty} {a} {b}) |].
  Notation "'Res' a b" := (mk_res a b)
      (in custom expr at level 2,
          a custom expr at level 4,
          b custom expr at level 4).

  Notation "'Nothing'" := (eApp (eConstr "option" "None") (eTy [!Result!]))
                      (in custom expr at level 0).

  Notation "'mkState' a b" :=
    [| {eConstr State "mkState_coq"} {a} {b} |]
      (in custom expr at level 0,
          a custom expr at level 1,
          b custom expr at level 1).


  (** New global context with the constants defined above (in addition to the ones defined in the Oak's "StdLib") *)

  Definition Σ' :=
    Prelude.Σ ++ [ Prelude.AcornMaybe;
           state_syn;
           msg_syn;
           addr_map_acorn;
           CounterBlockchain.CounterChainAcorn;
           CounterBlockchain.CounterContractCallContextAcorn;
           CounterBlockchain.CounterActionBodyAcorn;
           gdInd "Z" 0 [("Z0", []); ("Zpos", [(None,tyInd "positive")]);
                          ("Zneg", [(None,tyInd "positive")])] false].


  Notation "0 'z'" := (eConstr "Z" "Z0") (in custom expr at level 0).

End Notations.


Import Prelude.
(** Generating string constants for variable names *)

Run TemplateProgram (mkNames ["c";"s";"e";"m";"v";"dl"; "g"; "b"; "chain"; "n";
                              "tx_amount"; "bal"; "sender"; "own"; "isdone" ;
                              "accs"; "now";
                               "newstate"; "newmap"; "cond"] "").
(** A shortcut for [if .. then .. else ..]  *)
Notation "'if' cond 'then' b1 'else' b2 : ty" :=
  (eCase (Bool,[]) ty cond
         [(pConstr true_name [],b1);(pConstr false_name [],b2)])
    (in custom expr at level 4,
        cond custom expr at level 4,
        ty custom type at level 4,
        b1 custom expr at level 4,
        b2 custom expr at level 4).

Notation SCtx := "CounterContractCallContext".

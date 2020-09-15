(** * Data types for the crowdfunding contract tailored for extraction *)

Require Import String ZArith Basics.
From ConCert.Embedding Require Import Ast Notations PCUICTranslate Utils TranslationUtils.
From ConCert.Embedding.Examples Require Import Prelude.
From ConCert.Extraction.Examples Require Import PreludeExt SimpleBlockchainExt.

Require Import List PeanoNat ssrbool.

Import ListNotations.
From MetaCoq.Template Require Import All Loader.

Import MonadNotation.
Import BaseTypes.
Open Scope list.


Import AcornBlockchain.
Import PreludeExt.Maps.

(** Note that we define the deep embedding (abstract syntax trees) of the data structures and programs using notations. These notations are defined in  [Ast.v] and make use of the "custom entries" feature. *)

(** Brackets like [[\ \]] delimit the scope of data type definitions and like [[| |]] the scope of programs *)

(** Generating names for the data structures  *)
MetaCoq Run
        ( mp_ <- tmCurrentModPath tt ;;
          let mp := (PCUICTranslate.string_of_modpath mp_ ++ "@")%string in
          mkNames mp
             ["State" ; "mkState"; "balance" ; "donations" ; "owner";
              "deadline"; "goal"; "done";
              "Res" ; "Error";
             "msg"; "Action"; "Transfer"; "Empty" ] "_coq").
MetaCoq Run (mkNames "" ["Donate"; "GetFunds"; "Claim"] "_coq").

Import ListNotations.

(** ** Definitions of data structures for the contract *)

(** Parameters of the contract *)
Definition params_ty : type :=
  (* Deadline, Goal, Owner *)
  [! time × (money × address)!].

(** The internal state of the contract that is modified during the execution *)
Definition state_ty : type :=
  (* Contributions, Done *)
  [! Map × Bool !].

(** The full type of contract's internal state  *)
Definition full_state_ty :=
  [! {params_ty} × {state_ty} !].

(** Messages *)
Definition msg_syn :=
  [\ data msg =
       Donate [_]
     | GetFunds [_]
     | Claim [_] \].

MetaCoq Unquote Inductive (global_to_tc msg_syn).


(** ** Custom notations for projections from the state type *)

Notation "'get_params' st" :=
  [| first {params_ty} {state_ty} {st} |]
    (in custom expr at level 0).

Notation "'get_state' st" :=
  [| second {params_ty} {state_ty} {st} |]
    (in custom expr at level 0).

Notation "'deadline' st" :=
  [| first time (money × address) (get_params {st}) |]
    (in custom expr at level 0).

Notation "'goal' st" :=
  [| first money address (second time (money × address) (get_params {st})) |]
    (in custom expr at level 0).

Notation "'owner' st" :=
  [| second money address (second time (money × address) (get_params {st})) |]
    (in custom expr at level 0).

Notation "'contribs' st" :=
    [| first Map Bool (get_state {st}) |]
      (in custom expr at level 0).

Notation "'done' st" :=
  [| second Map Bool (get_state {st}) |]
    (in custom expr at level 0).

(** ** State "updates" *)

Notation "'mkFullState' prms st" :=
    [| Pair {params_ty} {state_ty} {prms} {st} |]
      (in custom expr at level 0,
          prms custom expr at next level,
          st custom expr at next level).

Notation "'mkParams' dl g o" :=
  [| Pair time (money × address) {dl} (Pair money address {g} {o}) |]
      (in custom expr at level 0,
          dl custom expr at next level,
          g custom expr at next level,
          o custom expr at next level).

Notation "'mkState' cs dn" :=
    [| Pair Map Bool {cs} {dn} |]
      (in custom expr at level 0,
          cs custom expr at next level,
          dn custom expr at next level).

Notation "'Result'" := [! Prod state_ty (List SimpleActionBody) !]
                         (in custom type at level 2).

Definition update_contribs_syn :=
  [| \"f_st" : {full_state_ty} => \"cs" : Map =>
     let "ps" : {params_ty} := get_params "f_st" in
     let "new_st" : {state_ty} := mkState "cs" (done "f_st") in
     mkFullState "ps" "new_st" |].

MetaCoq Unquote Definition update_contribs :=
  (expr_to_tc StdLib.Σ (indexify nil update_contribs_syn)).

Definition set_done_syn :=
  [| \"f_st" : {full_state_ty} =>
     let "ps" : {params_ty} := get_params "f_st" in
     let "new_st" : {state_ty} := mkState (contribs "f_st") True in
     mkFullState "ps" "new_st" |].

MetaCoq Unquote Definition set_done :=
  (expr_to_tc StdLib.Σ (indexify nil set_done_syn)).


(** ** Custom notations for projections from the call context and global state *)
Module Notations.

  Notation "'ctx_from' a" := [| {eConst "Ctx_from"} {a} |]
                             (in custom expr at level 0).
  Notation "'ctx_contract_address' a" :=
    [| {eConst "Ctx_contract_address"} {a} |]
      (in custom expr at level 0).
  Notation "'amount' a" := [| {eConst "Ctx_amount"} {a} |]
                             (in custom expr at level 0).

  (** New global context with the constants defined above (in addition to the ones defined in the Oak's "StdLib") *)

  Definition Σ' :=
    StdLib.Σ ++ [ Prelude.AcornMaybe;
           msg_syn;
           addr_map_acorn;
           AcornBlockchain.SimpleChainAcorn;
           AcornBlockchain.SimpleContractCallContextAcorn;
           AcornBlockchain.SimpleActionBodyAcorn;
           gdInd "Z" 0 [("Z0", []); ("Zpos", [(None,tyInd "positive")]);
                          ("Zneg", [(None,tyInd "positive")])] false].


End Notations.

(** Generating string constants for variable names *)

MetaCoq Run (mkNames "" ["c";"s";"e";"m";"v";"dl"; "g"; "chain"; "setup" ; "ctx" ;
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

Definition SCtx := to_string_name <% SimpleContractCallContext_coq %>.

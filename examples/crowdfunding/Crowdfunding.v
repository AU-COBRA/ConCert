(** We develop a deep embedding of a crowdfunding contract and prove some of its functional correctness properties using the corresponding shallow embedding *)

From ConCert.Embedding Require Import Ast.
From ConCert.Embedding Require Import Notations.
From ConCert.Embedding Require Import PCUICTranslate.
From ConCert.Embedding Require Import Prelude.
From ConCert.Embedding Require Import SimpleBlockchain.
From ConCert.Embedding Require Import TranslationUtils.
From ConCert.Examples.Crowdfunding Require Import CrowdfundingData.
From Coq Require Import String.
From MetaCoq.Template Require Import All.

Import MCMonadNotation.
Import BaseTypes.
Open Scope list.

Import Prelude.Maps.

(** Note that we define the deep embedding (abstract syntax trees) of the data structures and programs using notations. These notations are defined in [Ast.v] and make use of the "custom entries" feature. *)

(** Brackets like [[\ \]] delimit the scope of data type definitions and like [[| |]] the scope of programs *)


(** * The crowdfunding contract *)

Module CrowdfundingContract.

  Import AcornBlockchain.

  (** ** AST of the [init] function *)
  Module Init.
    Import CrowdfundingData.Notations.
    Definition crowdfunding_init : expr :=
      [| \c : SCtx => \dl : Nat => \g : Money => mkState 0z MNil dl (ctx_from c) False g |].

    MetaCoq Unquote Definition init :=
      (expr_to_tc Σ' (indexify nil crowdfunding_init)).

    (* Check init. *)
 End Init.

 (** ** AST of the [receive] function *)
  Module Receive.

   Import CrowdfundingData.Notations.

   (** We specialise some polymorphic constructors to avoid writing types all the time *)
   Notation "'#Just' a" := [| {eConstr (Utils.to_string_name <% option %>) "Some"} {eTy [! Result!]} {a}|]
                           (in custom expr at level 0,
                               a custom expr at level 1).

   Notation "'#Pair' a b" := [| {eConstr Prod "pair"}
                               {eTy (tyInd State)}
                               {eTy actions_ty} {a} {b} |]
                           (in custom expr at level 0,
                               a custom expr at level 1,
                               b custom expr at level 1).

   Notation "'#Nothing'" := (eApp (eConstr (Utils.to_string_name <% option %>) "None") (eTy [!Result!]))
                             (in custom expr at level 0).

   Definition SCtx := Utils.to_string_name <% SimpleContractCallContext_coq %>.
   Definition SChain := Utils.to_string_name <% SimpleChain_coq %>.

   Definition crowdfunding : expr :=
    [| \chain : SChain => \c : SCtx => \m : Msg => \s : State =>
         let bal : Money := balance s in
         let now : Nat := cur_time chain in
         let tx_amount : Money := amount c in
         let sender : Address := ctx_from c in
         let own : Address := owner s in
         let accs : Map := donations s in
         case m : Msg return Maybe Result of
            | GetFunds ->
             if (own ==n sender) && (deadline s <n now) && (goal s <= bal) then
               #Just (#Pair (mkState 0z accs own (deadline s) True (goal s))
                          [Transfer bal sender])
             else #Nothing : Maybe Result
           | Donate -> if now <=n deadline s then
             (case (mfind accs sender) : Maybe Money return Maybe Result of
               | Just v ->
                 let newmap : Map := madd sender (v + tx_amount) accs in
                 #Just (#Pair (mkState (tx_amount + bal) newmap own (deadline s) (done s) (goal s))
                            Nil)
               | Nothing ->
                 let newmap : Map := madd sender tx_amount accs in
                 #Just (#Pair (mkState (tx_amount + bal) newmap own (deadline s) (done s) (goal s))
                            Nil))
               else #Nothing : Maybe Result
           | Claim ->
             if (deadline s <n now) && (bal < goal s) && (~ done s) then
             (case (mfind accs sender) : Maybe Money return Maybe Result of
              | Just v -> let newmap : Map := madd sender 0z accs in
                  #Just (#Pair (mkState (bal-v) newmap own (deadline s) (done s) (goal s))
                       [Transfer v sender])
               | Nothing -> #Nothing)
              else #Nothing : Maybe Result
    |].

  MetaCoq Unquote Definition receive :=
    (expr_to_tc Σ' (indexify nil crowdfunding)).

  End Receive.
End CrowdfundingContract.

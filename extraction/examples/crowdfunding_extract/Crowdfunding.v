(**  We develop a deep embedding of a crowdfunding contract and prove some of its functional correctness properties using the corresponding shallow embedding *)

Require Import String ZArith Basics.
From ConCert.Embedding Require Import Ast Notations CustomTactics
     PCUICTranslate PCUICtoTemplate Utils MyEnv.

From ConCert.Extraction Require Import Liquidity.
From ConCert.Extraction.Examples Require Import Prelude CrowdfundingData SimpleBlockchain.

Require Import List PeanoNat ssrbool.

Import ListNotations.
From MetaCoq.Template Require Import All.

Import MonadNotation.
Import BaseTypes.
Open Scope list.

Import Lia.

(** Note that we define the deep embedding (abstract syntax trees) of the data structures and programs using notations. These notations are defined in  [Ast.v] and make use of the "custom entries" feature. *)

(** Brackets like [[\ \]] delimit the scope of data type definitions and like [[| |]] the scope of programs *)


(** * The crowdfunding contract *)

Module CrowdfundingContract.

  Import AcornBlockchain.

  (** Generating string constants for variable names *)

  Run TemplateProgram
      (mkNames ["c";"s";"e";"m";"v";"dl"; "g"; "chain"; "ctx"; "setup";
               "tx_amount"; "bal"; "sender"; "sent_by"; "own"; "isdone" ;
               "accs"; "now"; "newstate"; "newmap"; "cond" ] "").

  Notation "'Result'" := [!"prod"  ("list" "SimpleActionBody") {full_state_ty} !]
                           (in custom type at level 2).


  (** ** AST of the validation function *)
  Module Validate.
    Import Notations.

     Definition maybe_bind_unit_syn :=
     [| \"o" : Maybe Unit => \"b" : Maybe Result =>
        case "o" : Maybe Unit return Maybe Result of
        | Just "_" -> "b"
        | Nothing -> $Nothing$Maybe [:  Result ]  |].

   Make Definition maybe_bind_unit :=
     (expr_to_tc Σ' (indexify nil maybe_bind_unit_syn)).

   Notation "a >> b" :=
     [| {eConst "maybe_bind_unit"} {a} {b}|]
       (in custom expr at level 0,
           a custom expr,
           b custom expr).

   (** We check if the amount is zero and then let this check pass, otherwise return Nothing, meaning failure *)
   Definition validate_syn :=
     [| \tx_amount : money =>
        if 0z == tx_amount then $Just$Maybe [: Unit] star
        else $Nothing$Maybe [: Unit] : Maybe Unit |].

   Make Definition validate :=
     (expr_to_tc Σ' (indexify nil validate_syn)).


   Notation "'VALIDATE' amt" := [| {eConst "validate"} {amt} |] (in custom expr at level 0).

   End Validate.

  (** ** AST of the [init] function *)
  Module Init.
    Import Notations.
    Import Validate.

    (** The last argument of the [init] function must be a [CallCtx]. The init function returns an options type. The [init] function in Liquidity cannot refer to global definitions, so we have to inline validation *)
    Definition crowdfunding_init : expr :=
      [| \setup : {params_ty}  => \ctx : CallCtx =>
         (if sent_amount ctx == 0z then
            $Just$Maybe [:{full_state_ty}]
             (mkFullState setup (mkState MNil False))
          else $Nothing$Maybe [: {full_state_ty}] : Maybe  {full_state_ty})|].

    Make Definition init :=
      (expr_to_tc Σ' (indexify nil crowdfunding_init)).

    (** We prove that the initialisation fails if we send money on contact deployment. *)
    Lemma init_validated setup call_ctx :
      (sc_sent_amount call_ctx <> 0)%Z ->
      init setup call_ctx = None.
    Proof.
      intros H. destruct call_ctx as [curr_time [sender [tx_amount total_bal]]].
      unfold init,maybe_bind_unit. destruct ?;auto.
      cbn in *. unfold validate in *.
      rewrite Z.eqb_eq in *. lia.
    Qed.

 End Init.

 (** ** AST of the [receive] function *)
 Module Receive.

   Import CrowdfundingData.Notations.
   Import Validate.

(** Constructors. [Res] is an abbreviation for [Some (st, [action]) : option (State * list ActionBody)] *)

  Definition actions_ty := [! "list" "SimpleActionBody" !].

  Notation "'Transfer' a b" :=
    [| {eConstr SActionBody "Act_transfer"} {b} {a} |]
      (in custom expr at level 0,
          a custom expr at level 1,
          b custom expr at level 1).

  Definition eqb_addr (a1 a2 : address_coq) :=
    match a1, a2 with
    | ContractAddr_coq n1, ContractAddr_coq n2 => Nat.eqb n1 n2
    | UserAddr_coq n1, UserAddr_coq n2 => Nat.eqb n1 n2
    | _, _ => false
    end.

  Notation "a ==a b" := [| {eConst "eqb_addr"} {a} {b} |]
                        (in custom expr at level 0).


   (** We specialise some polymorphic constructors to avoid writing types all the time *)
   Notation "'#Just' a" := [| $Just$Maybe  [: Result ] {a}|]
                           (in custom expr at level 0,
                               a custom expr at level 1).

   Notation "'#Pair' a b" := [| $"pair"$"prod" [: {actions_ty}] [: {full_state_ty}] {a} {b} |]
                           (in custom expr at level 0,
                               a custom expr at level 1,
                               b custom expr at level 1).

   Notation "'#Nothing'" := (eApp (eConstr "option" "None") (eTy [!Result!]))
                              (in custom expr at level 0).

   Notation "'#Nil'" := [| {eConstr "list" "nil"} {eTy (tyInd SActionBody)} |]
                      (in custom expr at level 0).
   Notation "[ x ]" := [| {eConstr "list" "cons"} {eTy (tyInd SActionBody)} {x} #Nil |]
                        ( in custom expr at level 0,
                          x custom expr at level 1).


   Notation "'DONE'" := (eConst "set_done")
                          (in custom expr at level 0).
   Notation "'UPDATE_CONTRIBS'" := (eConst "update_contribs")
                                    (in custom expr at level 0).

   Definition lookup k m := lookup_map m k.

   Notation "'findm' a b" :=  [| {eConst "lookup"} {a} {b} |]
        (in custom expr at level 0,
            a custom expr at level 1,
            b custom expr at level 1).

   Definition crowdfunding : expr :=
     [|  \m : msg => \s : {full_state_ty}  => \ctx : CallCtx =>
         let sender : address := sender_addr ctx in
         let bal : money := acc_balance ctx in
         let tx_amount : money := sent_amount ctx in
         let now : time := current_time ctx in
         let own : address := owner s in
         let accs : Map := contribs s in
         case m : msg return Maybe Result of
            | GetFunds ->
              if (own ==a sender) && (deadline s <t now) && (goal s <= bal) then
                (VALIDATE tx_amount) >> (#Just (#Pair [Transfer bal sender] (DONE s)))
             else #Nothing : Maybe Result
            | Donate ->
              if now <=t deadline s then
                (case (findm sender accs) : Maybe money return Maybe Result of
                  | Just v ->
                    let newmap : Map := madd sender (v + tx_amount) accs in
                    #Just (#Pair #Nil (UPDATE_CONTRIBS s newmap))
                  | Nothing ->
                    let newmap : Map := madd sender tx_amount accs in
                    #Just (#Pair #Nil (UPDATE_CONTRIBS s newmap)))
              else #Nothing : Maybe Result
           | Claim ->
             if (deadline s <t now) && (bal < goal s) && (~ done s) then
             (case (findm sender accs) : Maybe money return Maybe Result of
              | Just v -> let newmap : Map := madd sender 0z accs in
                 (VALIDATE tx_amount) >> (#Just (#Pair [Transfer v sender] (UPDATE_CONTRIBS s newmap)))
              | Nothing -> #Nothing)
             else #Nothing : Maybe Result
    |].

  Make Definition receive :=
    (expr_to_tc Σ' (indexify nil crowdfunding)).

  (** We prove that the call to the [receive] fails (returns [None]) if the contract was called with non-zero amount and this is not the "donate" case*)
  Lemma receive_validated  message state
        (call_ctx :  SimpleCallCtx) :
    (sc_sent_amount call_ctx <> 0)%Z -> message <> Donate_coq ->
    receive message state call_ctx = None.
  Proof.
    intros Hneq Hmsg.
    destruct call_ctx as [curr_time [sender [tx_amount total_bal]]].
    cbn in *.
    destruct message;tryfalse.
    + simpl. destruct ?;auto.
      unfold maybe_bind_unit. destruct ?;auto.
      simpl in *. unfold validate in *.
      destruct ?;tryfalse.
      rewrite Z.eqb_eq in *. lia.
    + simpl. destruct ?;auto.
      destruct ?;auto.
      unfold maybe_bind_unit. destruct ?;auto.
      simpl in *. unfold validate in *.
      destruct ?;tryfalse.
      rewrite Z.eqb_eq in *. lia.
  Qed.

  End Receive.
End CrowdfundingContract.

Import CrowdfundingContract.

(** Packing together the data type definitions and functions *)
Definition CFModule : LiquidityModule :=
  {| datatypes := [msg_syn];
     storage := [! {full_state_ty} !];
     message := [! msg !];
     init := Init.crowdfunding_init;
     functions := [("update_contribs", update_contribs_syn);
                   ("maybe_bind_unit", Validate.maybe_bind_unit_syn);
                   ("validate", Validate.validate_syn);
                   ("set_done", set_done_syn);
                   ("receive", Receive.crowdfunding)
                  ];
     main := "receive";
     (* The last argument is a tuple corresponding to [SimpleCallCtx]*)
     main_extra_args :=
       [simpleCallCtx] |}.


(** A translation table for types *)
Definition TTty : env string :=
  [("Coq.Numbers.BinNums.Z", "tez");
   ("time_coq", "timestamp");
   ("address_coq", "address");
   ("addr_map", "(address,tez) map");
   ("Coq.Init.Datatypes.nat", "nat");
   ("SimpleActionBody", "operation")].

(** A translation table for primitive binary operations *)
Definition TT : env string :=
  [("Coq.ZArith.BinInt.Z.add", "addTez");
     ("Coq.ZArith.BinInt.Z.eqb", "eqTez");
     ("Coq.ZArith.BinInt.Z.leb", "lebTez");
     ("Coq.ZArith.BinInt.Z.ltb", "ltbTez");
     ("negb", "not");
     ("add_map", "Map.add");
     ("lookup", "Map.find")].

Compute liquidifyModule TT TTty CFModule.

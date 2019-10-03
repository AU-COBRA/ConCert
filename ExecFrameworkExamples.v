(** * Contract examples  *)

(** We develop some blockchain infrastructure relevant for the contract execution (a fragment of the standard library and an execution context). With that, we develop a deep embedding of a crowdfunding contract and prove some of its properties using the corresponding shallow embedding *)

Require Import String ZArith.
Require Import Ast CustomTactics TCTranslate.
Require Import List.
Require Import PeanoNat.
Require Import Coq.ssr.ssrbool.
Require Import Morphisms.

Require Import SmartContracts.Blockchain.
From SmartContracts Require Import Congress.

Import ListNotations.
From MetaCoq.Template Require Import All.

Import MonadNotation.
Import BaseTypes.
Open Scope list.

(** Our approximation for finite maps. Eventually, will be replaced with the Oak's standard library implementation. We assume that the standard library is available for a contract developer. *)

Import Serializable.

Section Maps.
  Open Scope nat.

  Definition addr_map_acorn :=
    [\ data "addr_map" := "mnil" : "addr_map" | "mcons" : Nat -> "Z" -> "addr_map" -> "addr_map"; \].

  Make Inductive (trans_global_dec addr_map_acorn).

  Fixpoint lookup_map (m : addr_map) (key : nat) : option Z :=
    match m with
    | mnil => None
    | mcons k v m' =>
      if (Nat.eqb key k) then Some v else lookup_map m' key
    end.

  (* Ported from FMapWeaklist of StdLib *)
  Fixpoint add_map (k : nat) (x : Z) (s : addr_map) : addr_map :=
  match s with
   | mnil => mcons k x mnil
   | mcons k' y l => if Nat.eqb k k' then mcons k x l else mcons k' y (add_map k x l)
  end.

  Definition inmap_map k m := match lookup_map m k with
                              | Some _ => true
                              | None => false
                              end.

  Lemma lookup_map_add k v m : lookup_map (add_map k v m) k = Some v.
  Proof.
    induction m.
    + simpl. now rewrite PeanoNat.Nat.eqb_refl.
    + simpl. destruct (k =? n) eqn:Heq.
      * simpl. now rewrite PeanoNat.Nat.eqb_refl.
      * simpl. now rewrite Heq.
  Qed.

  Fixpoint to_list (m : addr_map) : list (nat * Z)%type:=
    match m with
    | mnil => nil
    | mcons k v tl => cons (k,v) (to_list tl)
    end.

  Fixpoint of_list (l : list (nat * Z)) : addr_map :=
    match l with
    | nil => mnil
    | cons (k,v) tl => mcons k v (of_list tl)
    end.

  Lemma of_list_to_list m: of_list (to_list m) = m.
  Proof. induction m;simpl;congruence. Qed.

  Lemma to_list_of_list l: to_list (of_list l) = l.
  Proof. induction l as [ | x l'];simpl;auto.
         destruct x. simpl;congruence. Qed.

  Hint Rewrite to_list_of_list of_list_to_list : hints.

  Global Program Instance addr_map_serialize : Serializable addr_map :=
    {| serialize m := serialize (to_list m);
       deserialize l := option_map of_list (deserialize l); |}.
  Next Obligation.
    intros. cbn. rewrite deserialize_serialize. cbn.
    now autorewrite with hints.
  Defined.

End Maps.

Notation "a ∈ m" := (inmap_map a m = true) (at level 50).
Notation "a ∉ m" := (inmap_map a m = false) (at level 50).

(** Generation of string constants using MetaCoq *)
Fixpoint mkNames (ns : list string) (postfix : string) :=
  match ns with
  | [] => tmPrint "Done."
  | n :: ns' => n' <- tmEval all (n ++ postfix)%string ;;
                  str <- tmQuote n';;
                  tmMkDefinition n str;;
                  mkNames ns' postfix
  end.

(** Notations for functions on finite maps *)

Definition Map := "addr_map".

Notation "'MNil'" := [| {eConstr "addr_map" "mnil"} |]
                       (in custom expr at level 0).

Notation "'mfind' a b" :=  [| {eConst "lookup_map"} {a} {b} |]
        (in custom expr at level 0,
            a custom expr at level 1,
            b custom expr at level 1).

Notation "'madd' a b c" :=  [| {eConst "add_map"} {a} {b} {c} |]
        (in custom expr at level 0,
            a custom expr at level 1,
            b custom expr at level 1,
            c custom expr at level 1).

Notation "'mem' a b" :=  [| {eConst "inmap_map"} {a} {b} |]
        (in custom expr at level 0,
            a custom expr at level 1,
            b custom expr at level 1).

Module Prelude.

  Definition Σ : list global_dec :=
    [gdInd Unit 0 [("Coq.Init.Datatypes.tt", [])] false;
       gdInd Bool 0 [("true", []); ("false", [])] false;
       gdInd Nat 0 [("Z", []); ("Suc", [(None,tyInd Nat)])] false;
       gdInd "list" 1 [("nil", []); ("cons", [(None,tyRel 0);
                                                (None,tyApp (tyInd "list") (tyRel 0))])] false;
       gdInd "prod" 2 [("pair", [(None,tyRel 1);(None,tyRel 0)])] false].

  Notation "a + b" := [| {eConst "Coq.ZArith.BinInt.Z.add"} {a} {b} |]
                        (in custom expr at level 0).
  Notation "a * b" := [| {eConst "Coq.ZArith.BinInt.Z.mul"} {a} {b} |]
                        (in custom expr at level 0).
  Notation "a - b" := [| {eConst "Coq.ZArith.BinInt.Z.sub"} {a} {b} |]
                        (in custom expr at level 0).
  Notation "a == b" := [| {eConst "PeanoNat.Nat.eqb"} {a} {b} |]
                          (in custom expr at level 0).
  Notation "a < b" := [| {eConst "Coq.ZArith.BinInt.Z.ltb"} {a} {b} |]
                        (in custom expr at level 0).
  Notation "a <= b" := [| {eConst "Coq.ZArith.BinInt.Z.leb"} {a} {b} |]
                         (in custom expr at level 0).
  Notation "a <n b" := [| {eConst "PeanoNat.Nat.ltb"} {a} {b} |]
                        (in custom expr at level 0).
  Notation "a <=n b" := [| {eConst "PeanoNat.Nat.leb"} {a} {b} |]
                        (in custom expr at level 0).

  Notation "'Zero'" := (eConstr Nat "Z") ( in custom expr at level 0).
  Notation "'Suc'" := (eConstr Nat "Suc") ( in custom expr at level 0).
  Notation "0" := [| Zero |] ( in custom expr at level 0).
  Notation "1" := [| Suc Zero |] ( in custom expr at level 0).

  Notation "'Zero'" := (pConstr "Z" [])
                  (in custom pat at level 0).

  Notation "'Suc' x" := (pConstr "Suc" [x])
                    (in custom pat at level 0,
                        x constr at level 4).

  Notation "a && b" := [| {eConst "andb"} {a} {b} |]
                         (in custom expr at level 0).
  Notation "~ a" := [| {eConst "negb"} {a} |]
                        (in custom expr at level 0).

  Definition true_name := "true".
  Definition false_name := "false".
  Notation "'True'" := (pConstr true_name []) (in custom pat at level 0).
  Notation "'False'" := (pConstr false_name []) ( in custom pat at level 0).

  Notation "'Nil'" := (pConstr "nil" []) (in custom pat at level 0).
  Notation "'Cons' y z" := (pConstr "cons" [y;z])
                             (in custom pat at level 0,
                                 y constr at level 4,
                                 z constr at level 4).


  Notation "'True'" := (eConstr Bool true_name) (in custom expr at level 0).
  Notation "'False'" := (eConstr Bool false_name) ( in custom expr at level 0).

  Notation "'star'" :=
    (eConstr Unit "Coq.Init.Datatypes.tt")
      (in custom expr at level 0).

  Definition AcornList : global_dec :=
    gdInd "list" 1 [("nil", []);("cons", [(None, tyRel 0);(None, (tyApp (tyInd "list") (tyRel 0)))])] false.

  Notation List := "list".

  Definition AcornOption : global_dec :=
    gdInd "option" 1 [("Some", [(None, tyRel 0)]);("None", [])] false.

  Definition AcornProd : global_dec :=
    gdInd "prod" 2 [("pair", [(None, tyRel 1); (None, tyRel 0)])] false.

End Prelude.


(** * Contract execution context  *)

Module AcornBlockchain.

(** We create a simply-typed records and data types corresponding for
the actual definitions of [SmartContracts.Blockchain] which are paremeterised with [BaseTypes] *)

  Definition Address := Nat.
  Definition Money := "Coq.Numbers.BinNums.Z".


  Definition SimpleChainAcorn : global_dec :=
    [\ record "SimpleChain" :=
       "Build_chain" { "Chain_height" : "nat";
         "Current_slot" : "nat";
         "Finalized_height" : "nat";
         "Account_balance" : Address -> Money } \].

  Notation "'cur_time' a" := [| {eConst "Current_slot"} {a} |]
                               (in custom expr at level 0).

  Make Inductive (trans_global_dec SimpleChainAcorn).

  Definition SimpleContractCallContextAcorn : global_dec :=
    [\ record "SimpleContractCallContext" :=
       "Build_ctx" {
           (* Address sending the funds *)
           "Ctx_from" : Address;
           (* Address of the contract being called *)
           "Ctx_contract_address" : Address;
           (* Amount of currency passed in call *)
           "Ctx_amount" : Money} \].

  Notation "'ctx_from' a" := [| {eConst "Ctx_from"} {a} |]
                               (in custom expr at level 0).
  Notation "'ctx_contract_address' a" :=
    [| {eConst "Ctx_contract_address"} {a} |]
      (in custom expr at level 0).
  Notation "'amount' a" := [| {eConst "Ctx_amount"} {a} |]
                               (in custom expr at level 0).

  Make Inductive (trans_global_dec SimpleContractCallContextAcorn).

  Definition SimpleActionBodyAcorn : global_dec :=
    [\ data "SimpleActionBody" :=
          "Act_transfer" : Address -> Money -> "ActionBody"; \].

  Make Inductive (trans_global_dec SimpleActionBodyAcorn).

  Notation SActionBody := "SimpleActionBody".

End AcornBlockchain.


(** ** The crowdfunding contract *)

Module CrowdfundingContract.

  Import AcornBlockchain.

  (** Note that we define the deep embedding (abstract syntax trees) of the data structures and programs using notations. These notations are defined in  [Ast.v] and make use of the "custom entries" feature. The idea is that the corresponding ASTs will be produced from the real Oak programs by means of printing the fully annotated abstract syntax trees build from constructors of the inductive type [Ast.expr] *)

   (** Brackets like [[\ \]] delimit the scope of global definitions and like [[| |]] the scope of programs *)

  (** Generating names for the data structures  *)
  Run TemplateProgram
      (mkNames ["State" ; "mkState"; "balance" ; "donations" ; "owner"; "deadline"; "goal"; "done";
                "Res" ; "Error";
                "Msg"; "Donate"; "GetFunds"; "Claim";
                "Action"; "Transfer"; "Empty" ] "_coq").

  Import ListNotations.

  (** *** Definitions of data structures for the contract *)

  (** The internal state of the contract *)
  Definition state_syn : global_dec :=
    [\ record State :=
       mkState { balance : Money ;
         donations : Map;
         owner : Address;
         deadline : Nat;
         done : Bool;
         goal : Money } \].

  (** We can print actual AST by switching off the notations *)

  Unset Printing Notations.

  Print state_syn.
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
  Make Inductive (trans_global_dec state_syn).

  (** As a result, we get a new Coq record [State_coq] *)
  Print State_coq.

  Definition msg_syn :=
    [\ data Msg :=
         Donate : Msg
       | GetFunds : Msg
       | Claim : Msg; \].

  Make Inductive (trans_global_dec msg_syn).

  (** Custom notations for patterns, projections and constructors *)
  Module Notations.

    (** Patterns *)
    Notation "'Donate'" :=
      (pConstr Donate []) (in custom pat at level 0).
    Notation "'GetFunds'" :=
      (pConstr GetFunds []) ( in custom pat at level 0).

    Notation "'Claim'" :=
      (pConstr Claim []) ( in custom pat at level 0).

    Notation "'Just' x" :=
      (pConstr "Some" [x]) (in custom pat at level 0,
                               x constr at level 4).
    Notation "'Nothing'" := (pConstr "None" [])
                              (in custom pat at level 0).

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


    Notation "'Nil'" := [| {eConstr "list" "nil"} {eTy (tyInd SActionBody)} |]
                        (in custom expr at level 0).

    Notation " x ::: xs" := [| {eConstr "list" "cons"} {eTy (tyInd SActionBody)} {x} {xs} |]
                              ( in custom expr at level 0).

    Notation "[ x ]" := [| {eConstr "list" "cons"} {eTy (tyInd SActionBody)} {x} Nil |]
                          ( in custom expr at level 0,
                            x custom expr at level 1).
    (** Constructors. [Res] is an abbreviation for [Some (st, [action]) : option (State * list ActionBody)] *)



    Definition actions_ty := [! "list" "SimpleActionBody" !].

    Definition Result := tyApp (tyApp (tyInd "prod") (tyInd State)) actions_ty.
    Definition OResult := tyApp (tyInd "option") Result.

    Definition mk_res a b := [| {eConstr "option" "Some"} {eTy Result}
                                   ({eConstr "prod" "pair"} {eTy (tyInd State)}
                                   {eTy actions_ty}  {a} {b}) |].
    Notation "'Res' a b" := (mk_res a b)
        (in custom expr at level 0,
            a custom expr at level 1,
            b custom expr at level 1).

    Notation "'Error'" := (eApp (eConstr "option" "None") (eTy Result))
                        (in custom expr at level 0).

    Notation "'mkState' a b" :=
      [| {eConstr State "mkState_coq"} {a} {b} |]
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

    Definition Σ' :=
      Prelude.Σ ++ [ Prelude.AcornOption;
             state_syn;
             msg_syn;
             addr_map_acorn;
             AcornBlockchain.SimpleChainAcorn;
             AcornBlockchain.SimpleContractCallContextAcorn;
             AcornBlockchain.SimpleActionBodyAcorn;
             gdInd "Z" 0 [("Z0", []); ("Zpos", [(None,tyInd "positive")]);
                            ("Zneg", [(None,tyInd "positive")])] false].


    Notation "'ZeroZ'" := (eConstr "Z" "Z0") (in custom expr at level 0).
    End Notations.

  Import Notations.
  Import Prelude.
  (** Generating string constants for variable names *)

  Run TemplateProgram (mkNames ["c";"s";"e";"m";"v";"dl"; "g"; "ch";
                                "tx_amount"; "bal"; "sender"; "own"; "isdone" ;
                                "accs"; "now";
                                 "newstate"; "newmap"; "cond"] "").
  (** A shortcut for [if .. then .. else ..]  *)
  Notation "'if' cond 'then' b1 'else' b2 : ty" :=
    (eCase (Bool,[]) ty cond
           [(pConstr true_name [],b1);(pConstr false_name [],b2)])
      (in custom expr at level 2,
          cond custom expr at level 4,
          ty constr at level 4,
          b1 custom expr at level 4,
          b2 custom expr at level 4).

  Notation "'Ctx'" := "SimpleContractCallContext".

  Global Program Instance CB : ChainBase :=
    build_chain_base nat Nat.eqb _ _ _ _ Nat.odd. (* Odd addresses are addresses of contracts :) *)
  Next Obligation.
    eapply NPeano.Nat.eqb_spec.
  Defined.

  Definition to_chain (sc : SimpleChain) : Chain :=
    let '(Build_chain h s fh ab) := sc in build_chain h s fh ab.

  Definition of_chain (c : Chain) : SimpleChain :=
    let '(build_chain h s fh ab) := c in Build_chain h s fh ab.

  Definition to_action_body (sab : SimpleActionBody) : ActionBody :=
    match sab with
    | Act_transfer addr x => act_transfer addr x
    end.

  Definition to_contract_call_context (scc : SimpleContractCallContext) : ContractCallContext :=
    let '(Build_ctx from contr_addr am) := scc in build_ctx from contr_addr am.

  Definition of_contract_call_context (cc : ContractCallContext) : SimpleContractCallContext :=
    let '(build_ctx from contr_addr am) := cc in Build_ctx from contr_addr am.

  Definition of_state (st : State_coq) : Z * addr_map * nat * nat * bool * Z :=
    let '(mkState_coq b d o dl d' g):= st in (b,d,o,dl,d',g).

  Definition to_state (p : Z * addr_map * nat * nat * bool * Z) :=
    let '(b,d,o,dl,d',g) := p in mkState_coq b d o dl d' g.

  Lemma of_state_to_state p : of_state (to_state p) = p.
  Proof. now destruct p. Qed.

  Lemma to_state_of_state st : to_state (of_state st) = st.
  Proof. now destruct st. Qed.

  Global Program Instance State_serializable : Serializable State_coq :=
    {| serialize st := serialize (of_state st);
       deserialize p := option_map to_state (deserialize p); |}.
  Next Obligation.
    intros. cbn. rewrite deserialize_serialize. now destruct x.
  Defined.

  Definition of_msg (msg : Msg_coq) : unit + (unit + unit) :=
    match msg with
    | Donate_coq => inl tt
    | GetFunds_coq => inr (inl tt)
    | Claim_coq => (inr (inr tt))
    end.

  Definition to_msg (s : unit + (unit + unit)) : Msg_coq :=
    match s with
    | inl _ => Donate_coq
    | inr (inl _) => GetFunds_coq
    | inr (inr _) => Claim_coq
    end.

  Lemma of_msg_to_msg s : of_msg (to_msg s) = s.
  Proof. destruct s as [ | s'];try destruct s';destruct u;simpl;easy. Qed.

  Lemma to_msg_of_msg msg : to_msg (of_msg msg) = msg.
  Proof. destruct msg;easy. Qed.

  Global Program Instance Msg_serializable : Serializable Msg_coq :=
    {| serialize msg := serialize (of_msg msg);
       deserialize s := option_map to_msg (deserialize s); |}.
  Next Obligation.
    intros. cbn. rewrite deserialize_serialize. now destruct x.
  Defined.


  Module Init.
    Definition crowdfunding_init : expr :=
      [| \c : Ctx => \dl : Nat => \g : "Z" => mkState ZeroZ MNil dl (ctx_from c) False g |].

    Compute (expr_to_term Σ' (indexify nil crowdfunding_init)).

    Make Definition init :=
      (expr_to_term Σ' (indexify nil crowdfunding_init)).

    Check init.

    Definition Setup := (nat * Z)%type.

    Definition init_wrapper (f : SimpleContractCallContext -> nat -> Z -> State_coq):
      Chain (BaseTypes:=CB) -> ContractCallContext (BaseTypes:=CB) -> Setup -> option State_coq
      := fun c cc setup => Some (f (of_contract_call_context cc) setup.1 setup.2).

    Definition wrapped_init
      : Chain -> ContractCallContext -> Setup -> option State_coq
      := init_wrapper init.

 End Init.


  Module Receive.
    Import Prelude.

  (** *** The AST of a crowdfunding contract *)
  Definition crowdfunding : expr :=
    [| \ch : "SimpleChain" =>  \c : Ctx => \m : Msg => \s : State =>
         let bal : Money := balance s in
         let now : Nat := cur_time ch in
         let tx_amount : Money := amount c in
         let sender : Address := ctx_from c in
         let own : Address := owner s in
         let accs : Map := donations s in
         case m : (Msg,[]) return < OResult > of
            | GetFunds ->
             if (own == sender) && (deadline s <n now) && (goal s <= bal)  then
               Res (mkState ZeroZ accs own (deadline s) True (goal s))
                   ([Transfer bal sender])
             else Error : OResult
           | Donate -> if now <=n deadline s then
             (case (mfind accs sender) : ("option",[tyInd Money]) return <OResult> of
               | Just v ->
                 let newmap : Map := madd sender (v + tx_amount) accs in
                 Res (mkState (tx_amount + bal) newmap own (deadline s) (done s) (goal s)) Nil
               | Nothing ->
                 let newmap : Map := madd sender tx_amount accs in
                 Res (mkState (tx_amount + bal) newmap own (deadline s) (done s) (goal s)) Nil)
               else Error : OResult
           | Claim ->
             if (deadline s <n now) && (bal < goal s) && (~ done s) then
             (case (mfind accs sender) : ("option",[tyInd Money]) return <OResult> of
              | Just v -> let newmap : Map := madd sender ZeroZ accs in
                  Res (mkState (bal-v) newmap own (deadline s) (done s) (goal s))
                      ([Transfer v sender])
               | Nothing -> Error)
              else Error : OResult
    |].

  Compute (expr_to_term Σ' (indexify nil crowdfunding)).

  Make Definition receive :=
    (expr_to_term Σ' (indexify nil crowdfunding)).

  Definition receive_wrapper
             (f : SimpleChain ->
                  SimpleContractCallContext ->
                   Msg_coq -> State_coq -> option (State_coq × list SimpleActionBody)) :
    Chain -> ContractCallContext ->
    State_coq -> option Msg_coq -> option (State_coq × list ActionBody) :=
    fun ch cc st msg => match msg with
                       Some msg' => option_map (fun '(st0,acts) => (st0, map to_action_body acts)) (f (of_chain ch) (of_contract_call_context cc) msg' st)
                     | None => None
                     end.

  Definition wrapped_receive
    : Chain -> ContractCallContext -> State_coq -> option Msg_coq -> option (State_coq × list ActionBody)
    := receive_wrapper receive.
End Receive.


(* Taken from [Congress], because otherwise it is not visible after import *)
Ltac solve_contract_proper :=
  repeat
    match goal with
    | [ |- ?x _  = ?x _] => unfold x
    | [ |- ?x _ _ = ?x _ _] => unfold x
    | [ |- ?x _ _ _ = ?x _ _ _] => unfold x
    | [ |- ?x _ _ _ _ = ?x _ _ _ _] => unfold x
    | [ |- ?x _ _ _ _ = ?x _ _ _ _] => unfold x
    | [ |- ?x _ _ _ _ _ = ?x _ _ _ _ _] => unfold x
    | [ |- Some _ = Some _] => f_equal
    | [ |- pair _ _ = pair _ _] => f_equal
    | [ |- (if ?x then _ else _) = (if ?x then _ else _)] => destruct x
    | [ |- match ?x with | _ => _ end = match ?x with | _ => _ end ] => destruct x
    | [H: ChainEquiv _ _ |- _] => rewrite H in *
    | _ => subst; auto
    end.

Import FunctionalExtensionality.

Lemma init_proper :
  Proper (ChainEquiv ==> eq ==> eq ==> eq) Init.wrapped_init.
Proof. repeat intro; solve_contract_proper. Qed.

Lemma of_chain_proper :
  Proper (ChainEquiv ==> eq) of_chain.
Proof. repeat intro. unfold of_chain. destruct x,y;cbn in *. inversion H.
       cbn in *;subst. f_equal. now apply functional_extensionality.
Qed.

Lemma receive_proper :
  Proper (ChainEquiv ==> eq ==> eq ==> eq ==> eq) Receive.wrapped_receive.
Proof.
  repeat intro. unfold Receive.wrapped_receive,Receive.receive_wrapper.
  subst. destruct y2;auto.
  f_equal.
  (* TODO : chnage this to avoid funext *)
  (* unfold Receive.receive. repeat solve_contract_proper. *)
  f_equal. destruct x,y;solve_contract_proper;cbn.
  inversion H.
  cbn in *;subst. solve_contract_proper. solve_contract_proper. f_equal.
  now apply functional_extensionality.
Qed.

Print Instances Serializable.Serializable.


Definition contract : Contract Init.Setup Msg_coq State_coq :=
  build_contract Init.wrapped_init init_proper Receive.wrapped_receive receive_proper.


  Ltac inv_andb H := apply Bool.andb_true_iff in H;destruct H.
  Ltac split_andb := apply Bool.andb_true_iff;split.


  Open Scope nat.
  Open Scope bool.

  Import Lia.

  Definition deadline_passed now (s : State_coq) := s.(deadline_coq) <? now.

  Definition goal_reached (s : State_coq) := (s.(goal_coq) <=? s.(balance_coq))%Z.

  Definition funded now (s : State_coq) :=
    deadline_passed now s && goal_reached s.

  Lemma not_leb n m : ~~ (n <=? m) -> m <? n.
  Proof.
   intros.
   unfold Nat.ltb in *.
   unfold is_true in *. rewrite Bool.negb_true_iff in *.
   rewrite Nat.leb_gt in *. rewrite Nat.leb_le in *. lia.
  Qed.

  Lemma not_ltb n m : ~~ (n <? m) -> m <=? n.
  Proof.
   intros.
   unfold Nat.ltb in *.
   unfold is_true in *. rewrite Bool.negb_true_iff in *.
   rewrite Nat.leb_gt in *. rewrite Nat.leb_le in *. lia.
  Qed.


  Lemma Znot_leb n m : ~~ (n <=? m)%Z -> (m <? n)%Z.
  Proof.
   intros.
   unfold is_true in *. rewrite Bool.negb_true_iff in *.
   rewrite Z.leb_gt in *. now rewrite Z.ltb_lt in *.
  Qed.

  Lemma Znot_ltb n m : ~~ (n <? m)%Z -> (m <=? n)%Z.
  Proof.
   intros.
   unfold is_true in *. rewrite Bool.negb_true_iff in *.
   rewrite Z.ltb_nlt in *. rewrite Z.leb_le in *. lia.
  Qed.

  (** ** Properties of the crowdfunding contract *)

  (** This function is a simplistic execution environment that performs one step of execution *)
  Definition run (receive : State_coq -> option (State_coq * list SimpleActionBody) ) (init : State_coq)
    : State_coq * list SimpleActionBody :=
    match receive init with
    | Some (fin, out) => (fin, out)
    | None => (init, []) (* if an error occurs, the state remains the same *)
    end.

  (** A wrapper for the assertions about the contract execution *)
  Definition assertion (pre : State_coq -> Prop)
             (entry : State_coq -> option (State_coq * list SimpleActionBody))
             (post : State_coq -> list SimpleActionBody -> Prop) :=
    forall init, pre init -> exists fin out, run entry init = (fin, out) /\ post fin out.

  Notation "{{ P }} c {{ Q }}" := (assertion P c Q)( at level 50).


  (** The donations can be paid back to the backers if the goal is not
reached within a deadline *)

  Lemma get_money_back_guarantee CallCtx BC (sender := CallCtx.(Ctx_from)) v :
      (* pre-condition *)
      {{ fun init =>
         deadline_passed BC.(Current_slot) init
       /\ ~~ (goal_reached init)
       /\ ~~ init.(done_coq)
       /\ lookup_map init.(donations_coq) sender = Some v }}

        (* contract call *)
       Receive.receive BC CallCtx Claim_coq

       (* post-condition *)
       {{fun fin out => lookup_map fin.(donations_coq) sender = Some 0%Z
         /\ In (Act_transfer sender v) out}}.
  Proof.
    unfold assertion. intros init H. simpl.
    destruct H as [Hdl [Hgoal [Hndone Hlook]]].
    unfold deadline_passed,goal_reached in *;simpl in *.
    repeat eexists. unfold run. simpl.
    assert (balance_coq init <? goal_coq init = true)%Z by now apply Znot_leb.
    repeat destruct (_ <? _)%Z;tryfalse. destruct (_ <? _);tryfalse.
    destruct (~~ done_coq _)%bool;tryfalse.
    destruct (lookup_map _ _);tryfalse;inversion Hlook;subst;clear Hlook.
    repeat split;cbn. apply lookup_map_add. now constructor.
  Qed.

  (** New donations are recorded correctly in the contract's state *)

  Lemma new_donation_correct CallCtx BC (sender := CallCtx.(Ctx_from))
        (donation := CallCtx.(Ctx_amount)) :

    {{ fun init =>
          sender ∉ init.(donations_coq) (* the sender have not donated before *)
       /\ ~~ deadline_passed BC.(Current_slot) init }}

      (* contract call *)
    Receive.receive BC CallCtx Donate_coq

    {{ fun fin out =>
         (* nothing gets transferred *)
         out = []
         (* donation has been accepted *)
         /\ lookup_map fin.(donations_coq) sender = Some donation  }}.
  Proof.
    unfold assertion. intros init H. simpl.
    destruct H as [Hnew_sender Hdl].
    unfold deadline_passed in *;simpl in *.
    unfold run.
    repeat eexists.
    simpl in *. apply not_ltb in Hdl.
    destruct (_ <=? _);tryfalse.
    unfold inmap_map in *.
    destruct (lookup_map _ _);tryfalse.
    repeat split;eauto. simpl. now rewrite lookup_map_add.
  Qed.


  (** Existing donations are updated correctly in the contract's state *)

  Lemma existing_donation_correct BC CallCtx (sender := CallCtx.(Ctx_from))
        (new_don := CallCtx.(Ctx_amount)) old_don :
    {{ fun init =>
         (* the sender has already donated before *)
         lookup_map init.(donations_coq) sender = Some old_don

       /\ ~~ deadline_passed BC.(Current_slot) init }}

     Receive.receive BC CallCtx Donate_coq

    {{ fun fin out =>
         (* nothing gets transferred *)
         out = []
         (* donation has been added *)
       /\ lookup_map fin.(donations_coq) sender = Some (old_don + new_don)%Z }}.
  Proof.
    unfold assertion. intros init H. simpl.
    subst sender new_don.
    destruct H as [Hsender Hdl].
    unfold deadline_passed in *;simpl in *.
    subst;simpl in *.
    eexists. eexists.
    unfold run. simpl in *. apply not_ltb in Hdl.
    destruct (_ <=? _);tryfalse.
    destruct (lookup_map _ _);tryfalse.
    inversion Hsender;subst.
    repeat split;simpl;eauto. now rewrite lookup_map_add.
  Qed.

  Fixpoint sum_map (m : addr_map) : Z :=
    match m with
    | mnil => 0
    | mcons _ v m' => v + sum_map m'
    end.

  Lemma sum_map_add_in m : forall n0 (v' v : Z) k,
      lookup_map m k = Some n0 ->
      sum_map m = v ->
      sum_map (add_map k (n0+v') m) = (v' + v)%Z.
  Proof.
    intros;subst.
    revert dependent n0. revert v' k.
    induction m;intros;subst.
    + inversion H.
    + simpl in *. destruct (k =? n) eqn:Hkn.
      * simpl in *. inversion H. subst. lia.
      * simpl in *. rewrite IHm;auto. lia.
  Qed.

  Lemma sum_map_add_not_in m : forall v' v k,
      lookup_map m k = None ->
      sum_map m = v ->
      sum_map (add_map k v' m) = (v' + v)%Z.
  Proof.
    intros;subst.
    revert dependent k. revert v'.
    induction m;intros;subst.
    + reflexivity.
    + simpl in *. destruct (k =? n) eqn:Hkn.
      * inversion H.
      * simpl in *. rewrite IHm;auto. lia.
  Qed.

  (** The contract does no leak funds: the overall balance before the deadline is always equal to the sum of individual donations *)

  Definition consistent_balance BC state :=
    ~~ deadline_passed BC.(Current_slot) state /\
    sum_map state.(donations_coq) = state.(balance_coq).

  (** This lemma holds for any message  *)
  Lemma contract_backed BC CallCtx msg :

    {{ consistent_balance BC }}

      Receive.receive BC CallCtx msg

    {{ fun fin _ => consistent_balance BC fin }}.
  Proof.
    intros init H.
    destruct H as [Hdl Hsum].
    destruct msg.
    + (* Donate *)
      simpl in *.
      specialize Hdl as Hdl'.
      unfold deadline_passed in Hdl. unfold run,consistent_balance.
      apply not_ltb in Hdl.  simpl.
      destruct (_ <=? _);tryfalse.
      destruct (lookup_map _ _) eqn:Hlook.
      * repeat eexists;eauto. now apply sum_map_add_in.
      * repeat eexists;eauto. now apply sum_map_add_not_in.
    + (* GetFunds - it is not possible to get funds before the deadline, so the state is not modified *)
      unfold consistent_balance in *.
      unfold deadline_passed in *.
      exists init. exists []. unfold run. simpl.
      destruct (_ <? _);tryfalse. rewrite Bool.andb_false_r. simpl.
      split;eauto.
    + (* Claim - it is not possible to claim a donation back before the deadline, so the state is not modified *)
      unfold consistent_balance in *.
      unfold deadline_passed in *.
      exists init. exists []. unfold run. simpl.
      destruct (_ <? _);tryfalse. simpl.
      split;eauto.
  Qed.

  (** The owner gets the money after the deadline, if the goal is reached *)

  Lemma GetFunds_correct BC CallCtx (OwnerAddr := CallCtx.(Ctx_from)) (funds : Z) :
    {{ fun init => funded BC.(Current_slot) init
       /\ init.(owner_coq) =? OwnerAddr
       /\ balance_coq init = funds }}

    Receive.receive BC CallCtx GetFunds_coq

    {{ fun fin out =>
       (* the money are sent back *)
       In (Act_transfer OwnerAddr funds) out
       (* set balance to 0 after withdrawing by the owner *)
       /\  fin.(balance_coq) = 0%Z
       (* set the "done" flag *)
       /\ fin.(done_coq) = true}}.
  Proof.
    unfold assertion. intros init H. simpl.
    destruct H as [Hfunded [Hown Hbalance]]. unfold funded,goal_reached,deadline_passed in *.
    subst. simpl in *.
    unfold run. simpl in *. subst OwnerAddr. eexists. eexists.
    destruct (_ <? _);tryfalse. destruct ( _ =? _);tryfalse. simpl in *.
    destruct (_ <=? _)%Z;tryfalse. repeat split;eauto.
    now constructor.
  Qed.

  (** Backers cannot claim their money if the campaign have succeed (but owner haven't claimed the money yet, so the "done" flag is not set to [true]) *)
  Lemma no_claim_if_succeeded BC CallCtx the_state:
    {{ fun init =>
         funded BC.(Current_slot) init
         /\ ~~ init.(done_coq)
         /\ init = the_state }}

      Receive.receive BC CallCtx Claim_coq

    (* Nothing happens - the stated stays the same and no outgoing transfers *)
    {{ fun fin out => fin = the_state /\ out = [] }}.
  Proof.
    unfold assertion. intros init H. simpl.
    unfold funded,deadline_passed,goal_reached in *. subst. simpl in *.
    destruct H as [Hdl [Hgoal Hst]].
    inv_andb Hdl. subst. unfold run. simpl.
    exists the_state. eexists.
    destruct the_state as [i_balance i_dons i_own i_dl i_done i_goal].
    destruct CallCtx as [from c_addr am now]. simpl in *.

    destruct (_ <? _);tryfalse.
    replace (i_balance <? i_goal)%Z with false by
        (symmetry;rewrite Z.ltb_ge in *; rewrite Z.leb_le in *;lia).
    now simpl.
  Qed.

  (** Backers cannot claim their money if the contract is marked as "done" *)
  Lemma no_claim_after_done BC CallCtx the_state :
    {{ fun init => init.(done_coq) /\ init = the_state }}

     Receive.receive BC CallCtx Claim_coq
    (* Nothing happens - the stated stays the same and no outgoing transfers *)
    {{ fun fin out => fin = the_state /\ out = [] }}.
  Proof.
    unfold assertion. intros init H. simpl. destruct H. subst.
    unfold funded,deadline_passed,goal_reached in *. subst. simpl in *.
    exists the_state. eexists.
    unfold run. simpl in *. destruct (done_coq _);tryfalse. simpl in *.
    now rewrite Bool.andb_false_r.
  Qed.
End CrowdfundingContract.

Require Import String.
Require Import Ast.
Require Import EvalE.
Require Import List.
Import ListNotations.
From Template Require Import All.


Import MonadNotation.
Import BaseTypes.
Import StdLib.
Open Scope list.
(* Example by Jakob *)
(* Definition receive *)
(*            (chain : PackedChain) *)
(*            (ctx : ContractCallContext) *)
(*            (state : State) *)
(*            (msg : option Msg) : option (State * list ActionBody) := *)
(*   match msg with *)
(*   | Some msg_payme => *)
(*     let sender := ctx_from ctx in *)
(*     let me := ctx_contract_address ctx in *)
(*     do amount <- FMap.find sender (money_owed state); *)
(*       Some (state, *)
(*             [act_transfer sender amount; *)
(*              act_call me 0 (msg_continuation1 (build_continuation1 sender amount))]) *)
(*   | Some (msg_continuation1 (build_continuation1 sender amount)) => *)
(*     Some (state<|money_owed ::= FMap.add sender 0|>, []) *)
(* end. *)

Definition Address := nat.
Definition Action := unit.

Record ctx := mkctx { _ctx_from : Address; _ctx_contract_address : Address}.

Module BalanceContract.
  Record state := st { _balance : nat; _owner : Address }.
  Inductive result :=
  | res : state -> Action -> result
  | error.

  Inductive msg :=
  | topup | withdraw.


  Module ConstantMapping.

    Definition Address := "Coq.Init.Datatypes.nat".
    Definition Money := "Coq.Init.Datatypes.nat".
    Definition Result := "ExampleContracts.BalanceContract.result".
    Definition Action := Unit.


    Definition Msg := "ExampleContracts.BalanceContract.msg".
    Notation "'Topup'" := (pConstr "ExampleContracts.BalanceContract.Topup" []) (in custom pat at level 0).
    Notation "'Withdraw'" := (pConstr "ExampleContracts.BalanceContract.Withdraw" []) ( in custom pat at level 0).

    Definition State := "ExampleContracts.BalanceContract.state".
    Notation "'balance' a" :=
      [| {eConst "ExampleContracts.BalanceContract._balance"} {a} |]
        (in custom expr at level 0).
    Notation "'owner' a" :=
      [| {eConst "ExampleContracts.BalanceContract._owner"} {a} |]
        (in custom expr at level 0).

    Notation "'Res' a b" :=
      [| {eConstr Result "ExampleContracts.BalanceContract.res"} {a} {b} |]
        (in custom expr at level 0,
            a custom expr at level 1,
            b custom expr at level 1).

    Notation "'St' a b" :=
      [| {eConstr State "ExampleContracts.BalanceContract.st"} {a} {b} |]
        (in custom expr at level 0,
            a custom expr at level 1,
            b custom expr at level 1).

    Definition Ctx := "ExampleContracts.ctx".
    Notation "'ctx_from' a" := [| {eConst "ExampleContracts._ctx_from"} {a} |]
                                 (in custom expr at level 0).
    Notation "'ctx_contract_address' a" :=
      [| {eConst "ExampleContracts._ctx_contract_address"} {a} |]
        (in custom expr at level 0).

    Notation "'Error'" := (eConstr Result "ExampleContracts.BalanceContract.error")
                        (in custom expr at level 0).

    (* New global context with the constants defined above (in addition to the ones defined in
       "StdLib") *)
    Definition Σ' :=
    Σ ++ [gdInd Ctx [("ExampleContracts.mkctx", [tyInd Address; tyInd Address])];
            gdInd "ExampleContracts.BalanceContract.state"
                  [("ExampleContracts.BalanceContract.st", [tyInd Address; tyInd Money])];
            gdInd "ExampleContracts.BalanceContract.result"
                  [("ExampleContracts.BalanceContract.res", [tyInd State; tyInd Action]);
                     ("ExampleContracts.BalanceContract.error", [])];
            gdInd "ExampleContracts.BalanceContract.msg"
                  [("ExampleContracts.BalanceContract.Topup",[]);
                     ("ExampleContracts.BalanceContract.Withdraw",[])]].


    End ConstantMapping.

  Import ConstantMapping.

  Module Names.
    (* Create a macro "define_names" using TemplateMonad *)
    Definition c := "c".
    Definition s := "s".
    Definition e := "e".
    Definition m := "m".
    Definition amount := "amount".
    Definition sender := "sender".
    Definition own := "own".
    Definition newstate := "newstate".
    Definition cond := "cond".
  End Names.

  Import Names.

  Notation "'if' cond 'then' b1 'else' b2" :=
    (eCase (Bool,0) (tyInd Result) cond
           [(pConstr true_name [],b1);(pConstr false_name [],b2)])
      (in custom expr at level 0,
          cond custom expr at level 4,
          b1 custom expr at level 4,
          b2 custom expr at level 4).

  Definition contract : expr :=
    [|
     \c : Ctx ->
          \s : State ->
               \m : Msg ->
                    case m : Msg return Result of
                      | Withdraw ->
                         let amount : Money := balance s in
                         let sender : Address := ctx_from c in
                         let own : Address := owner s in
                         if own == sender then Res (St Z own) star else Error
                      | Topup -> Error
    |].

  Make Definition entry :=
      Eval compute in (expr_to_term Σ' (indexify nil contract)).

  End BalanceContract.

  Import BalanceContract.

  Definition OwnerAddr := 123.
  Definition CntrAddr := 321.

  Definition CallCtx := mkctx OwnerAddr CntrAddr.

  Lemma withdraw_correct (init_state final_state: state) msg out_tx :
    (* pre-condition *)
    init_state.(_balance) > 0 ->
    init_state.(_owner) = OwnerAddr ->
    msg = withdraw ->

    entry CallCtx init_state msg = res final_state out_tx ->

    (* post-condition (TODO: add a post-condition about the outgoing transaction) *)
    final_state.(_balance) = 0.
  Proof.
    intros Hb Hi Hmsg Hcall. subst. simpl in *.
    destruct (Nat.eqb (_owner init_state) OwnerAddr).
    + inversion Hcall. easy.
    + inversion Hcall.
  Qed.
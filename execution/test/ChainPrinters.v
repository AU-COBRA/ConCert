From ConCert.Execution Require Import Blockchain.
From ConCert.Execution Require Import Serializable.
From ConCert.Execution Require Import BoundedN.
From ConCert.Execution Require Import ChainedList.
From ConCert.Execution Require Import ResultMonad.
From ConCert.Execution.Test Require Import LocalBlockchain.
From ConCert.Execution.Test Require Import TestUtils.

From QuickChick Require Import QuickChick. Import QcNotation.

From Coq Require Import ZArith.
From Coq Require Import List. Import ListNotations.
Import BoundedN.Stdpp.

Definition Base := TestUtils.LocalChainBase.

Close Scope address_scope.
Open Scope list_scope.
Open Scope string_scope.


Definition sep : string := ", ".

(* Derive Show for positive. *)
Derive Show for SerializedType.

Derive Show for result.

#[export]
Instance showActionEvaluationError
    `{Show (@Address Base)}
    `{Show SerializedValue}
    : Show ActionEvaluationError :=
{|
  show err :=
    match err with
    | amount_negative amount => "cannot transfer negative amount(" ++ show amount ++ ")"
    | amount_too_high amount => "cannot transfer amount(" ++
        show amount ++ ")" ++ "larger than users' balance"
    | no_such_contract addr => "no contract found with address: " ++ show addr
    | too_many_contracts => "too many contracts; no unused addresses left"
    | init_failed err => "init failed with error: " ++ show err
    | receive_failed err => "receive failed with error: " ++ show err
    | deserialization_failed val => "failed deserializing value"
    | internal_error => "internal error"
    end
|}.

#[export]
Instance showContract
          {Setup Msg State Error: Type}
          `{Serializable Setup}
          `{Serializable Msg}
          `{Serializable State}
          `{Serializable Error}
          : Show (Contract Setup Msg State Error) :=
{|
  show c := "Contract{...}"
|}.

#[export]
Instance showEnvironment
          (BaseTypes : ChainBase)
          `{Show Chain}
          : Show Environment :=
{|
  show env := "Environment{"
              ++ "chain: " ++ show (env_chain env) ++ sep
              ++ "contract states:..." ++ "}"
|}.

Fixpoint string_of_interp_type (st : SerializedType) : (interp_type st) -> string :=
match st as st0 return interp_type st0 -> string with
  | ser_unit => fun _ => "()"
  | ser_int => fun t => show t
  | ser_bool => fun t => show t
  | ser_list a =>
    fun t : list (interp_type a) =>
      let t_str_list := map (string_of_interp_type a) t in
      "[" ++ String.concat "; " t_str_list ++ "]"
  | ser_pair a b =>
    fun t : (interp_type a * interp_type b) =>
      "("
      ++ string_of_interp_type a (fst t)
      ++ ","
      ++ string_of_interp_type b (snd t) ++ ")"
  end.

Definition ex_serialized_type := ser_pair (ser_list (ser_list ser_bool)) ser_int.
(* Compute (interp_type ex_serialized_type). *)

Definition ex_val := ([[true; false]; [true; true]; [false]; []], 2%Z).
(* Compute (string_of_interp_type ex_serialized_type ex_val). *)

(* Show and Generator instances for types related to
   Traces (an execution sequence of contracts on the BC) *)
#[export]
Instance showBlockHeader
          (BaseTypes : ChainBase)
          `{Show (@Address BaseTypes)}
          : Show (@BlockHeader BaseTypes) :=
  {|
    show bh :=
      "BlockHeader{" ++ "bheight: "     ++ show (block_height bh)           ++ sep
                     ++ "bslot: "       ++ show (block_slot bh)             ++ sep
                     ++ "bfin_height: " ++ show (block_finalized_height bh) ++ sep
                     ++ "breward: "     ++ show (block_reward bh)           ++ sep
                     ++ "bcreator: "    ++ show (block_creator bh)          ++ "}"
  |}.

(* We dont show the bound because it may be a very large number which,
    when converted to nat and then to string, gives a memory overflow. *)
#[export]
Instance showBoundedN
          {bound : N}
          `{Show N}
          : Show (BoundedN.BoundedN bound) :=
{|
  show bn :=
    match bn with
    | BoundedN.bounded n _ => show n ++ "%" ++ show bound
    end
|}.

#[export]
Instance showBoundedNAddrSize : Show (BoundedN.BoundedN AddrSize) :=
{|
  show := @show (BoundedN.BoundedN AddrSize) showBoundedN
|}.

#[export]
Instance showAddress : Show (@Address Base) :=
{|
  show := @show (BoundedN.BoundedN AddrSize) showBoundedNAddrSize
|}.

#[export]
Instance showLocalChain : Show (@LocalChain AddrSize) :=
{|
  show lc := "LocalChain{"
              ++ show (lc_height lc) ++ sep
              ++ show (lc_slot lc) ++ sep
              ++ show (lc_fin_height lc)
              ++ sep ++ "... }"
|}.

#[export]
Instance showLocalContractCallContext : Show (@ContractCallContext Base) :=
{|
show cctx := "ContractCallContext{"
             ++ "ctx_from: " ++ show (@ctx_from Base cctx) ++ sep
             ++ "ctx_contract_addr: " ++ show (@ctx_contract_address Base cctx) ++ sep
             ++ "ctx_contract_balance: " ++ show (@ctx_contract_balance Base cctx) ++ sep
             ++ "ctx_amount: " ++ show (@ctx_amount Base cctx) ++ "}"
|}.

#[export]
Instance showActionBody
          `{Show SerializedValue}
          : Show ActionBody :=
{|
  show a := match a with
    | act_transfer addr amount =>
      "(act_transfer " ++ show addr ++ sep ++ show amount ++ ")"
    | act_call addr amount ser_value =>
      "(act_call " ++ show addr ++ sep ++ show amount ++ sep ++ show ser_value ++ ")"
    | act_deploy amount contract ser_value =>
      "(act_deploy " ++ show amount ++ sep ++ show ser_value ++ ")"
    end
|}.

#[export]
Instance showLocalAction
          `{Show ActionBody}
          : Show (@Action Base) :=
{|
  show a := "Action{"
            ++ "act_from: " ++ show (act_from a) ++ sep
            ++ "act_body: " ++ show (act_body a) ++ "}"
|}.

#[export]
Instance showLocalActionList
          `{Show (@Action Base)}
          : Show (list (@Action Base)) :=
{|
  show a := String.concat (";" ++ nl) (map show a)
|}.
#[export]
Existing Instance showLocalActionList | 0.

#[export]
Instance showOptLocalActionList
          `{Show (option (@Action Base))}
          : Show (list (option (@Action Base))) :=
{|
  show a := String.concat (";" ++ nl) (map show a)
|}.
#[export]
Existing Instance showOptLocalActionList | 0.

#[export]
Instance showChainState
          `{Show Environment}
          `{Show (@Action Base)}
          : Show (@ChainState Base) :=
{|
  show a := "ChainState{"
            ++ "env: " ++ show a.(chain_state_env) ++ sep
            ++ "queue: " ++ show a.(chain_state_queue) ++ "}"
|}.

#[export]
Instance showContractCallInfo
          {Msg : Type}
          `{Show Msg}
          : Show (ContractCallInfo Msg) :=
{|
  show info := "ContractCallInfo{"
                ++ "call_from: " ++ show (call_from info) ++ sep
                ++ "call_amount: " ++ show (call_amount info) ++ sep
                ++ "call_msg: " ++ show (call_msg info) ++ sep ++ "}"
|}.

(* Show instanced related to ChainedLists and ChainTraces *)

#[export]
Instance showAddBlockError
          `{Show (@Action Base)}
          `{Show SerializedValue}
          : Show AddBlockError :=
{|
  show err :=
    match err with
    | invalid_header header => "invalid_header: " ++ show header
    | invalid_root_action act => "invalid_root_action: " ++ show act
    | origin_from_mismatch act => "origin_from_mismatch: " ++ show act
    | action_evaluation_depth_exceeded => "action_evaluation_depth_exceeded"
    | action_evaluation_error act eval_error =>
      "action_evaluation_error for " ++ show act ++ " with error: " ++ show eval_error
    end
|}.

#[export]
Instance showChainTraceI
          `{Show (@Action Base)}
          {from to : ChainState}
          : Show (ChainTrace from to) :=
{|
  show :=
    let fix showChainTrace {from to : ChainState} (trace : ChainTrace from to) :=
      match trace with
      | snoc trace' step =>
      match step with
      | Blockchain.step_block _ _ _ _ _ _ _ _ =>
          let '(_, next_bstate) := chainstep_states step in
          showChainTrace trace' ++ nl ++
          "Block " ++ show next_bstate.(current_slot) ++ " [" ++ nl ++
            show next_bstate.(chain_state_queue)
          ++ "]; "
        | _ => showChainTrace trace'
        end
      | clnil => ""
      end in
    showChainTrace
|}.

#[export]
Instance showLCB
          `{Show (@Action Base)}
          : Show ChainBuilder :=
{|
  show cb := "Chain{| " ++ nl
             ++ show cb.(lcb_trace)
             ++ "|}" ++ nl
|}.

#[export]
Instance showChainBuilderType
          {BaseTypes : ChainBase}
          : Show (@ChainBuilderType BaseTypes) :=
  {| show a := "ChainBuilderType{...}" |}.

#[export]
Instance showChain (BaseTypes : ChainBase) : Show Chain :=
{|
  show c :=
    let height := show (chain_height c) in
    let slot := show (current_slot c) in
    let fin_height := show (finalized_height c) in
      "Chain{" ++ "height: "        ++ height     ++ sep
                ++ "current slot: " ++ slot       ++ sep
                ++ "final height: " ++ fin_height ++ "}"
|}.

Ltac make_show ts :=
  match ts with
  | (?t, ?tail) =>
    let rest := make_show tail in
    constr:(
      fun (v : SerializedValue) =>
        match @deserialize t _ v with
        | Some v => show v
        | None => rest v
        end)
  | tt => constr:(fun (v : SerializedValue) => "<FAILED DESERIALIZATION>")
  end.

(** Tactic to automatically derive [Show] instances for [SerializedValue].
    Takes as input a list of types and will produce a show instance that
    tries to deserialize the serialized value to one of those types and
    print that value. The instance will attempt to deserialize to the types
    in the order that they are given. Prints an error message in case all
    deserializations failed. The tactic will fail if the types given do not
    have [Show] and [Serializable] instances.
*)
Notation "'Derive' 'Show' 'Msg' < c0 , .. , cn >" :=
  (let pairs := pair c0 .. (pair cn tt) .. in
   ltac:(
     match goal with
     | [pairs := ?x |- _] =>
      let s := make_show x in
      let s' := eval cbn beta in s in
        exact {| show := s' |}
     end))
    (at level 0, c0, cn at level 9, only parsing).

#[export]
Instance showChainTraceSigT `{Show SerializedValue}
                            : Show {to : ChainState & ChainTrace empty_state to} :=
{|
  show a := show (projT2 a)
|}.

Close Scope string_scope.
Close Scope list_scope.

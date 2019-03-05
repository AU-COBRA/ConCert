From Coq Require Import ZArith.
From SmartContracts Require Import Blockchain.
From SmartContracts Require Import Oak.
From SmartContracts Require Import Monads.
From Containers Require Import Maps.
From Coq Require Import List.

Import ListNotations.
(* Note that [ ] or nil is needed for the empty list
   in this file as [] parses an empty map *)

Local Record ContractInstance :=
  {
    inst_state_ty : OakType;
    inst_msg_ty : OakType;
    inst_state : interp_type inst_state_ty;
    inst_receive : ContractCallContext -> interp_type inst_state_ty ->
                   option (interp_type inst_msg_ty) -> ChainAction;
  }.

Local Record ChainUpdate :=
  {
    upd_block : Block;
    (* Contracts that had their states updated and the new state *)
    upd_contracts : Map[Address, ContractInstance];
    (* Contracts deployed in this block *)
    upd_deployments : Map[Address, ContractDeployment];
    (* All transactions caused by update, including internal txs
       (due to contract execution) *)
    upd_txs : list Tx;
  }.

Inductive LocalChain :=
  {
    lc_updates : list ChainUpdate;
  }.

Definition genesis_block : Block :=
  {| block_header := {| block_number := 0; |};
     block_txs := nil |}.

Definition initial_chain : LocalChain :=
  {| lc_updates :=
       [{| upd_block := genesis_block;
           upd_contracts := []%map;
           upd_deployments := []%map;
           upd_txs := nil |}]
  |}.

Definition lc_chain_at (lc : LocalChain) (bid : BlockId) : option LocalChain :=
  let is_old u := u.(upd_block).(block_header).(block_number) <=? bid in
  let new_updates := filter is_old lc.(lc_updates) in
  match new_updates with
  | hd :: tl => if hd.(upd_block).(block_header).(block_number) =? bid
                then Some {| lc_updates := new_updates |}
                else None
  | nil => None
  end.

Definition lc_block_at (lc : LocalChain) (bid : BlockId) : option Block :=
  let blocks := map upd_block lc.(lc_updates) in
  find (fun b => b.(block_header).(block_number) =? bid) blocks.

Definition lc_head_block (lc : LocalChain) : Block :=
  match lc.(lc_updates) with
  | hd :: _ => hd.(upd_block)
  | nil => genesis_block
  end.

Definition lc_incoming_txs (lc : LocalChain) (addr : Address) : list Tx :=
  let all_txs := flat_map (fun u => u.(upd_block).(block_txs)) lc.(lc_updates) in
  let is_inc tx := (tx.(tx_to) =? addr)%address in
  filter is_inc all_txs.

Definition lc_outgoing_txs (lc : LocalChain) (addr : Address) : list Tx :=
  let all_txs := flat_map (fun u => u.(upd_block).(block_txs)) lc.(lc_updates) in
  let is_out tx := (tx.(tx_from) =? addr)%address in
  filter is_out all_txs.

Local Definition find_first {A : Type} (f : ChainUpdate -> option A) (lc : LocalChain)
  : option A :=
  let opts := map f lc.(lc_updates) in
  let is_some o := match o with | Some _ => true | None => false end in
  match filter is_some opts with
  | hd :: _ => hd
  | _ => None
  end.

Definition lc_contract_deployment (lc : LocalChain) (addr : Address)
  : option ContractDeployment :=
  find_first (fun u => u.(upd_deployments)[addr]%map) lc.
  
Definition lc_contract_state (lc : LocalChain) (addr : Address)
  : option OakValue :=
  let get_state_oak_value u :=
      do c <- u.(upd_contracts)[addr]%map;
      Some (build_oak_value c.(inst_state_ty) c.(inst_state)) in
  find_first get_state_oak_value lc.

Definition local_chain_impl : ChainInterface :=
  {| ifc_chain_type := LocalChain;
     ifc_chain_at := lc_chain_at;
     ifc_head_block := lc_head_block;
     ifc_incoming_txs := lc_incoming_txs;
     ifc_outgoing_txs := lc_outgoing_txs;
     ifc_contract_deployment := lc_contract_deployment;
     ifc_contract_state := lc_contract_state;
  |}.
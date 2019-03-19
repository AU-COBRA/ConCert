From Coq Require Import ZArith.
From SmartContracts Require Import Blockchain.
From SmartContracts Require Import Oak.
From SmartContracts Require Import Monads.
From SmartContracts Require Import Containers.
From SmartContracts Require Import Extras.
From RecordUpdate Require Import RecordUpdate.
From Coq Require Import List.

Import RecordSetNotations.
Import ListNotations.

Record ChainUpdate :=
  build_chain_update {
    (* Contracts that had their states updated and the new state *)
    upd_contracts : FMap Address OakValue;
    (* All transactions caused by update, including internal txs
       (due to contract execution) *)
    upd_txs : list Tx;
  }.

Instance eta_chain_update : Settable _ :=
  mkSettable
    ((constructor build_chain_update) <*> upd_contracts
                                      <*> upd_txs)%settable.

(* Contains information about the chain that contracts should have access
   to. This does not contain definitions of contracts, for instance. *)
Record LocalChain :=
  build_local_chain {
    (* List of blocks and updates. Generally such lists have the
       same length, except during contract execution, where lc_updates
       is one ahead of lc_blocks (to facilitate tracking state within
       the block) *)
    lc_blocks : list Block;
    lc_updates : list ChainUpdate;
  }.

Instance eta_local_chain : Settable _ :=
  mkSettable
    ((constructor build_local_chain) <*> lc_blocks
                                     <*> lc_updates)%settable.

(* Contains full information about a chain, including contracts *)
Record LocalChainBuilder :=
  build_local_chain_builder {
    lcb_lc : LocalChain;
    lcb_ftxs : list (BlockId * FullTx);
  }.

Instance eta_local_chain_builder : Settable _ :=
  mkSettable
    ((constructor build_local_chain_builder) <*> lcb_lc
                                             <*> lcb_ftxs)%settable.

Definition genesis_block : Block :=
  {| block_header := {| block_number := 0; |};
     block_txs := [] |}.

Definition initial_chain_builder : LocalChainBuilder :=
  {| lcb_lc := {| lc_blocks := [genesis_block];
                  lc_updates :=
                    [{| upd_contracts := FMap.empty;
                        upd_txs := [] |}] |};
     lcb_ftxs := [];
  |}.

Definition lc_chain_at (lc : LocalChain) (bid : BlockId) : option LocalChain :=
  let is_old '(b, u) := b.(block_header).(block_number) <=? bid in
  let zipped := rev (combine (rev lc.(lc_blocks)) (rev lc.(lc_updates))) in
  let zipped_at := filter is_old zipped in
  let '(at_blocks, at_updates) := split zipped_at in
  match at_blocks with
  | hd :: _ => if hd.(block_header).(block_number) =? bid
                then Some {| lc_blocks := at_blocks; lc_updates := at_updates; |}
                else None
  | [] => None
  end.

Definition lc_block_at (lc : LocalChain) (bid : BlockId) : option Block :=
  let blocks := lc.(lc_blocks) in
  find (fun b => b.(block_header).(block_number) =? bid) blocks.

Definition lc_head_block (lc : LocalChain) : Block :=
  match lc.(lc_blocks) with
  | hd :: _ => hd
  | [] => genesis_block
  end.

Definition lc_incoming_txs (lc : LocalChain) (addr : Address) : list Tx :=
  let all_txs := flat_map (fun u => u.(upd_txs)) lc.(lc_updates) in
  let is_inc tx := (tx.(tx_to) =? addr)%address in
  filter is_inc all_txs.

Definition lc_outgoing_txs (lc : LocalChain) (addr : Address) : list Tx :=
  let all_txs := flat_map (fun u => u.(upd_txs)) lc.(lc_updates) in
  let is_out tx := (tx.(tx_from) =? addr)%address in
  filter is_out all_txs.

Definition lc_contract_state (lc : LocalChain) (addr : Address)
  : option OakValue :=
  find_first (fun u => FMap.find addr u.(upd_contracts)) lc.(lc_updates).

Definition lc_interface : ChainInterface :=
  {| ci_type := LocalChain;
     ci_chain_at := lc_chain_at;
     ci_head_block := lc_head_block;
     ci_incoming_txs := lc_incoming_txs;
     ci_outgoing_txs := lc_outgoing_txs;
     ci_contract_state := lc_contract_state;
  |}.


Section ExecuteActions.
  Context (initial_lcb : LocalChainBuilder).

  Record ExecutionContext :=
    build_execution_context {
      new_ftxs : list FullTx;
      new_update : ChainUpdate;
    }.

  Instance eta_execution_context : Settable _ :=
    mkSettable
      ((constructor build_execution_context) <*> new_ftxs
                                             <*> new_update)%settable.

  Let make_acc_lcb (ec : ExecutionContext) : LocalChainBuilder :=
    let new_lc := (initial_lcb.(lcb_lc))[[lc_updates ::= cons ec.(new_update)]] in
    let new_bid := new_lc.(lc_head_block).(block_header).(block_number) + 1 in
    let new_bftxs := map (fun t => (new_bid, t)) ec.(new_ftxs) in
    {| lcb_lc := new_lc; lcb_ftxs := new_bftxs ++ initial_lcb.(lcb_ftxs) |}.

  Let make_acc_c (lcb : LocalChainBuilder) : Chain :=
    build_chain lc_interface lcb.(lcb_lc).

  Let verify_amount (c : Chain) (addr : Address) (amt : Amount)
    : option unit :=
    if (amt <=? account_balance c addr)%nat
    then Some tt
    else None.

  Let find_contract (addr : Address) (lcb : LocalChainBuilder)
    : option WeakContract :=
    let to_wc (t : BlockId * FullTx) : option WeakContract :=
        let (bid, ft) := t in
        if ft.(ftx_to) =? addr then
          match ft.(ftx_body) with
          | ftx_deploy wc _ => Some wc
          | _ => None
          end
        else
          None in
    find_first to_wc lcb.(lcb_ftxs).

  Let count_contract_deployments (lcb : LocalChainBuilder) : nat :=
    let is_deployment (t : BlockId * FullTx) : bool :=
        match (snd t).(ftx_body) with
        | ftx_deploy _ _ => true
        | _ => false
        end in
    length (filter is_deployment lcb.(lcb_ftxs)).

  Let verify_no_txs (addr : Address) (lcb : LocalChainBuilder) : option unit :=
    match incoming_txs (make_acc_c lcb) addr with
    | _ :: _ => None
    | [] => Some tt
    end.

  Fixpoint execute_action
          (act : Address (*from*) * ChainAction)
          (ec : ExecutionContext)
          (gas : nat)
          (is_internal : bool)
          {struct gas}
    : option ExecutionContext :=
    match gas, act with
    | 0, _ => None
    | S gas, (from, act) =>
      let acc_lcb := make_acc_lcb ec in
      let acc_c := make_acc_c acc_lcb in
      let deploy_contract amount (wc : WeakContract) setup :=
          do verify_amount acc_c from amount;
          let contract_addr := 1 + count_contract_deployments acc_lcb in (* todo *)
          do verify_no_txs contract_addr acc_lcb;
          let ctx := {| ctx_chain := acc_c;
                        ctx_from := from;
                        ctx_contract_address := contract_addr;
                        ctx_amount := amount |} in
          let (ver, init, recv) := wc in
          do state <- init ctx setup;
          let new_ftx := {| ftx_from := from;
                            ftx_to := contract_addr;
                            ftx_amount := amount;
                            ftx_body := ftx_deploy wc setup;
                            ftx_is_internal := is_internal; |} in
          let new_cu :=
              ec.(new_update)[[upd_contracts ::= FMap.add contract_addr state]]
                             [[upd_txs ::= cons (new_ftx : Tx)]] in
          let new_ec :=
              ec[[new_update := new_cu]]
                [[new_ftxs ::= cons new_ftx]] in
          Some new_ec in

      let send_or_call to amount msg_opt :=
          do verify_amount acc_c from amount;
          let new_ftx := {| ftx_from := from;
                            ftx_to := to;
                            ftx_amount := amount;
                            ftx_body :=
                              match msg_opt with
                              | Some msg => ftx_call msg
                              | None => ftx_empty
                              end;
                            ftx_is_internal := is_internal; |} in
          let new_cu := ec.(new_update)[[upd_txs ::= cons (new_ftx : Tx)]] in
          let new_ec := ec[[new_update := new_cu]][[new_ftxs ::= cons new_ftx]] in
          match find_contract to acc_lcb with
          | None => match msg_opt with
                    | Some _ => None (* Sending message to non-contract *)
                    | None => Some new_ec
                    end
          | Some wc =>
            let acc_lcb := make_acc_lcb new_ec in
            let acc_c := make_acc_c acc_lcb in
            let contract_addr := to in
            do state <- lc_contract_state acc_lcb.(lcb_lc) contract_addr;
            let (ver, init, recv) := wc in
            let ctx := {| ctx_chain := acc_c;
                          ctx_from := from;
                          ctx_contract_address := contract_addr;
                          ctx_amount := amount |} in
            do '(new_state, resp_actions) <- recv ctx state msg_opt;
            let new_cu :=
                ec.(new_update)[[upd_contracts ::= FMap.add to new_state]]
                               [[upd_txs ::= cons (new_ftx : Tx)]] in
            let new_ec := ec[[new_update := new_cu]][[new_ftxs ::= cons new_ftx]] in
            let fix go acts cur_ec :=
                match acts with
                  | [] => Some cur_ec
                  | hd :: tl =>
                    do cur_ec <- execute_action (contract_addr, hd) cur_ec gas true;
                    go tl cur_ec
                end in
            go resp_actions new_ec
          end in

      match act with
      | act_deploy amount wc setup => deploy_contract amount wc setup
      | act_transfer to amount => send_or_call to amount None
      | act_call to amount msg => send_or_call to amount (Some msg)
      end
    end.

  Definition execute_actions
             (coinbase : FullTx)
             (actions : list (Address * ChainAction))
             (gas : nat)
    : option LocalChainBuilder :=
    let fix go acts ec :=
        match acts with
        | [] => Some ec
        | hd :: tl =>
          do ec <- execute_action hd ec gas false;
          go tl ec
        end in
    let empty_ec := {| new_ftxs := [coinbase];
                       new_update := {| upd_contracts := FMap.empty;
                                        upd_txs := [coinbase : Tx] |}; |} in
    do ec <- go actions empty_ec;
    let new_lcb := make_acc_lcb ec in
    let recorded_txs := map_option (fun ftx => if ftx.(ftx_is_internal) then
                                                 Some (ftx : Tx)
                                               else
                                                 None) ec.(new_ftxs) in
    let hdr := {| block_number := length (initial_lcb.(lcb_lc).(lc_blocks)) |} in
    let block := build_block hdr recorded_txs in
    (* make_acc_lcb will have done all updates except adding the actual block *)
    let new_lcb := new_lcb[[lcb_lc := new_lcb.(lcb_lc)[[lc_blocks ::= cons block]]]] in
    Some new_lcb.
End ExecuteActions.

(* Adds a block to the chain by executing the specified chain actions.
   Returns the new chain if the execution succeeded (for instance,
   transactions need enough funds, contracts should not reject, etc. *)
Definition add_block
           (lcb : LocalChainBuilder)
           (coinbase : Address)
           (actions : list (Address (*from*) * ChainAction))
  : option LocalChainBuilder :=
  let coinbase_ftx :=
      {| ftx_from := 0;
         ftx_to := coinbase;
         ftx_amount := 50;
         ftx_body := ftx_empty;
         ftx_is_internal := false; |} in
  execute_actions lcb coinbase_ftx actions 10.

Definition lc_builder_interface : ChainBuilderInterface :=
  {| cbi_chain_interface := lc_interface;
     cbi_type := LocalChainBuilder;
     cbi_chain lcb := lcb.(lcb_lc);
     cbi_initial := initial_chain_builder;
     cbi_add_block := add_block;
     cbi_all_txs lcb := rev (map snd lcb.(lcb_ftxs))
  |}.

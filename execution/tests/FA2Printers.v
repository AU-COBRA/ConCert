From ConCert Require Import Blockchain LocalBlockchain.
From ConCert Require Import FA2Interface FA2Token.
From ConCert Require Import Serializable.
From ConCert.Execution.QCTests Require Import ChainGens TestUtils ChainPrinters.
Require Import Strings.String.
From QuickChick Require Import QuickChick.
Local Open Scope string_scope.

(* Instance showtoken_id : Show token_id :=
{|
	show v := show v
|}. *)

Instance showCallback {A : Type}: Show (FA2Interface.callback A) :=
{|
	show v := "callback"
|}.

Instance showFA2InterfaceTransfer : Show FA2Interface.transfer :=
{|
  show t := "Transfer{" 
            ++ "from_: " ++ show t.(from_) ++ sep 
            ++ "to_: " ++ show t.(to_) 
            ++ "transfer_token_id: " ++ show t.(transfer_token_id) 
            ++ "amount: " ++ show t.(amount) 
            ++ "}"
|}.

Instance showFA2Interfacebalance_of_request : Show FA2Interface.balance_of_request :=
{|
  show t := "balance_of_request{" 
            ++ "owner: " ++ show t.(owner) ++ sep 
            ++ "bal_req_token_id: " ++ show t.(bal_req_token_id) 
            ++ "}"
|}.

Instance showFA2Interfacebalance_of_response : Show FA2Interface.balance_of_response :=
{|
  show t := "balance_of_response{" 
            ++ "request: " ++ show t.(request) ++ sep 
            ++ "balance: " ++ show t.(balance) 
            ++ "}"
|}.

Instance showFA2Interfacebalance_of_param : Show FA2Interface.balance_of_param :=
{|
  show t := "balance_of_param{" 
            ++ "bal_requests: " ++ show t.(bal_requests) ++ sep 
            ++ "bal_callback: " ++ show t.(bal_callback) 
            ++ "}"
|}.

Instance showFA2Interfacetotal_supply_response : Show FA2Interface.total_supply_response :=
{|
  show t := "total_supply_response{" 
            ++ "supply_resp_token_id: " ++ show t.(supply_resp_token_id) ++ sep 
            ++ "total_supply: " ++ show t.(total_supply) 
            ++ "}"
|}.

Instance showFA2Interfacetotal_supply_param : Show FA2Interface.total_supply_param :=
{|
  show t := "total_supply_param{" 
            ++ "supply_param_token_ids: " ++ show t.(supply_param_token_ids) ++ sep 
            ++ "supply_param_callback: " ++ show t.(supply_param_callback) 
            ++ "}"
|}.

Instance showFA2Interfacetoken_metadata : Show FA2Interface.token_metadata :=
{|
  show t := "token_metadata{" 
            ++ "metadata_token_id: " ++ show t.(metadata_token_id) ++ sep 
            ++ "metadata_decimals: " ++ show t.(metadata_decimals) 
            ++ "}"
|}.

Instance showFA2Interfacetoken_metadata_param : Show FA2Interface.token_metadata_param :=
{|
  show t := "token_metadata_param{" 
            ++ "metadata_token_ids: " ++ show t.(metadata_token_ids) ++ sep 
            ++ "metadata_callback: " ++ show t.(metadata_callback) 
            ++ "}"
|}.

Instance showoperator_tokens : Show operator_tokens :=
{|
	show m := match m with
						| all_tokens => "all_tokens"
						| some_tokens token_ids => "some_tokens " ++ show token_ids
						end
|}.

Instance showFA2Interfaceoperator_param : Show FA2Interface.operator_param :=
{|
  show t := "operator_param{" 
            ++ "op_param_owner: " ++ show t.(op_param_owner) ++ sep 
            ++ "op_param_operator: " ++ show t.(op_param_operator) ++ sep 
            ++ "op_param_tokens: " ++ show t.(op_param_tokens) ++ sep 
            ++ "}"
|}.

Instance showupdate_operator : Show update_operator :=
{|
	show m := match m with
						| add_operator param => "add_operator " ++ show param 
						| remove_operator param => "remove_operator " ++ show param
						end
|}.

Instance showFA2Interfaceis_operator_response : Show FA2Interface.is_operator_response :=
{|
  show t := "is_operator_response{" 
            ++ "operator: " ++ show t.(operator) ++ sep 
            ++ "is_operator: " ++ show t.(is_operator) 
            ++ "}"
|}.

Instance showFA2Interfaceis_operator_param : Show FA2Interface.is_operator_param :=
{|
  show t := "is_operator_param{" 
            ++ "is_operator_operator: " ++ show t.(is_operator_operator) ++ sep 
            ++ "is_operator_callback: " ++ show t.(is_operator_callback) 
            ++ "}"
|}.

Instance showself_transfer_policy : Show self_transfer_policy :=
{|
	show m := match m with
						| self_transfer_permitted => "self_transfer_permitted " 
						| self_transfer_denied => "self_transfer_denied "
						end
|}.

Instance showoperator_transfer_policy : Show operator_transfer_policy :=
{|
	show m := match m with
						| operator_transfer_permitted => "operator_transfer_permitted " 
						| operator_transfer_denied => "operator_transfer_denied "
						end
|}.

Instance showowner_transfer_policy : Show owner_transfer_policy :=
{|
	show m := match m with
						| owner_no_op => "owner_no_op " 
						| optional_owner_hook => "optional_owner_hook "
						| required_owner_hook => "required_owner_hook "
						end
|}.

(* Instance showFA2Interfacecustom_permission_policy : Show FA2Interface.custom_permission_policy :=
{|
  show t := "custom_permission_policy{" 
            ++ "custom_policy_config_api: " ++ show t.(custom_policy_config_api) 
            ++ "}"
|}. *)

Instance showFA2Interfacepermissions_descriptor : Show FA2Interface.permissions_descriptor :=
{|
  show t := "permissions_descriptor{" 
            ++ "descr_self: " ++ show t.(descr_self) ++ sep 
            ++ "descr_operator: " ++ show t.(descr_operator) ++ sep 
            ++ "descr_receiver: " ++ show t.(descr_receiver) ++ sep 
            ++ "descr_sender: " ++ show t.(descr_sender) ++ sep 
            ++ "descr_custom: " ++ show t.(descr_custom) 
            ++ "}"
|}.

Instance showFA2Interfacetransfer_descriptor : Show FA2Interface.transfer_descriptor :=
{|
  show t := "transfer_descriptor{" 
            ++ "transfer_descr_from_: " ++ show t.(transfer_descr_from_) ++ sep 
            ++ "transfer_descr_to_: " ++ show t.(transfer_descr_to_) ++ sep 
            ++ "transfer_descr_token_id: " ++ show t.(transfer_descr_token_id) ++ sep 
            ++ "transfer_descr_amount: " ++ show t.(transfer_descr_amount) 
            ++ "}"
|}.

Instance showFA2Interfacetransfer_descriptor_param : Show FA2Interface.transfer_descriptor_param :=
{|
  show t := "transfer_descriptor_param{" 
            ++ "transfer_descr_fa2: " ++ show t.(transfer_descr_fa2) ++ sep 
            ++ "transfer_descr_batch: " ++ show t.(transfer_descr_batch) ++ sep 
            ++ "transfer_descr_operator: " ++ show t.(transfer_descr_operator) 
            ++ "}"
|}.

Instance showfa2_token_receiver : Show fa2_token_receiver :=
{|
	show m := match m with
						| tokens_received param => "tokens_received " ++ show param 
						end
|}.

Instance showfa2_token_sender : Show fa2_token_sender :=
{|
	show m := match m with
						| tokens_sent param => "tokens_sent " ++ show param 
						end
|}.

Instance showFA2Interfaceset_hook_param : Show FA2Interface.set_hook_param :=
{|
  show t := "set_hook_param{" 
            ++ "hook_addr: " ++ show t.(hook_addr) ++ sep 
            ++ "hook_permissions_descriptor: " ++ show t.(hook_permissions_descriptor) 
            ++ "}"
|}.

Instance showFA2ReceiverMsg {Msg : Type} 
                           `{serMsg : Serializable Msg} 
                           `{Show Msg} 
                           : Show (@FA2ReceiverMsg _ Msg serMsg) :=
{|
	show m := match m with
						| receive_balance_of_param param => "receive_balance_of_param " ++ show param 
						| receive_total_supply_param param => "receive_total_supply_param " ++ show param 
						| receive_metadata_callback param => "receive_metadata_callback " ++ show param 
						| receive_is_operator param => "receive_is_operator " ++ show param 
						| receive_permissions_descriptor param => "receive_permissions_descriptor " ++ show param 
						| other_msg msg => show msg 
						end
|}.

Instance showFA2TokenMsg : Show FA2Token.Msg :=
{|
	show m := match m with
						| msg_transfer param => "transfer " ++ show param 
						| msg_set_transfer_hook param => "set_transfer_hook " ++ show param 
						| msg_balance_of param => "balance_of " ++ show param 
						| msg_total_supply param => "total_supply " ++ show param 
						| msg_token_metadata param => "token_metadata " ++ show param 
						| msg_permissions_descriptor param => "permissions_descriptor " ++ show param 
						| msg_update_operators param => "update_operators " ++ show param 
						| msg_is_operator param => "is_operator " ++ show param 
						| msg_receive_hook_transfer param => "receive_hook_transfer " ++ show param 
						end
|}.

Instance showFA2TokenLedger : Show FA2Token.TokenLedger :=
{|
  show t := "Token_Ledger{" 
            ++ "fungible: " ++ show t.(fungible) ++ sep 
            ++ "balances: " ++ show t.(balances) 
            ++ "}"
|}.

Instance showFA2State : Show FA2Token.State :=
{|
  show t := "FA2TokenState{" 
            ++ "fa2_owner: " ++ show t.(fa2_owner) ++ sep 
            ++ "assets: " ++ show t.(assets) ++ sep 
            ++ "operators: " ++ show t.(operators) ++ sep 
            ++ "tokens_metadata: " ++ show t.(tokens) ++ sep 
            ++ "transfer_hook: " ++ show t.(transfer_hook_addr) ++ sep 
            ++ "permission_policy: " ++ show t.(permission_policy) 
            ++ "}"
|}.

Instance showFA2Setup : Show FA2Token.Setup :=
{|
  show t := "FA2TokenSetup{" 
            ++ "setup_total_supply: " ++ show t.(setup_total_supply) ++ sep 
            ++ "tokens_metadata: " ++ show t.(setup_tokens) ++ sep 
            ++ "permission_policy: " ++ show t.(initial_permission_policy) 
            ++ "}"
|}.
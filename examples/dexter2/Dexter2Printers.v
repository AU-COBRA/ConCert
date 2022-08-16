From ConCert.Execution Require Import Blockchain.
From ConCert.Execution Require Import Serializable.
From ConCert.Execution.Test Require Import QCTest.
From ConCert.Examples.FA2 Require Import FA2Token.
From ConCert.Examples.FA2 Require Import FA2Printers.
From ConCert.Examples.Dexter2 Require Import Dexter2CPMM.
From ConCert.Examples.Dexter2 Require Import Dexter2FA12.

Local Open Scope string_scope.

(** * Dexter2 CPMM printers *)
Module NullAddressLocalBlockcain <: NullAddress.
  Definition BaseTypes : ChainBase := LocalChainBase.
  Definition null_address := creator.
  Definition set_delegate_call := (fun _ : @baker_address BaseTypes => @nil (@ActionBody BaseTypes)).
  Lemma delegate_call : forall addr, List.Forall (fun action => 
      match action with
      | act_transfer _ _ => False
      | act_call _ _ _ => False
      | act_deploy _ _ _ => False
      end) (set_delegate_call addr).
  Proof.
    now unfold set_delegate_call.
  Qed.
End NullAddressLocalBlockcain.
Module DEX2 := Dexter2 DSInstances NullAddressLocalBlockcain.

Instance showAddLiqduidityParam : Show add_liquidity_param :=
{|
  show p := "params{" ++ 
    "owner: " ++ show p.(owner) ++ sep ++
    "min lqt minted: " ++ show p.(minLqtMinted) ++ sep ++
    "max tokens deposited: " ++ show p.(maxTokensDeposited) ++ sep ++
    "deadline: " ++ show p.(add_deadline) ++ "}"
|}.

Instance showRemoveLiqduidityParam : Show remove_liquidity_param :=
{|
  show p := "params{" ++ 
    "to: " ++ show p.(liquidity_to) ++ sep ++
    "lqt burned: " ++ show p.(lqtBurned) ++ sep ++
    "min xtz withdrawn: " ++ show p.(minXtzWithdrawn) ++ sep ++
    "min tokens withdrawn: " ++ show p.(minTokensWithdrawn) ++ sep ++
    "deadline: " ++ show p.(remove_deadline) ++ "}"
|}.

Instance showXtzToTokenParam : Show xtz_to_token_param :=
{|
  show p := "params{" ++ 
    "to: " ++ show p.(tokens_to) ++ sep ++
    "min tokens bought: " ++ show p.(minTokensBought) ++ sep ++
    "deadline: " ++ show p.(xtt_deadline) ++ "}"
|}.

Instance showTokenToXtzParam : Show token_to_xtz_param :=
{|
  show p := "params{" ++ 
    "to: " ++ show p.(xtz_to) ++ sep ++
    "tokens sold: " ++ show p.(tokensSold) ++ sep ++
    "min xtz bought: " ++ show p.(minXtzBought) ++ sep ++
    "deadline: " ++ show p.(ttx_deadline) ++ "}"
|}.

Instance showSetBakerParam : Show set_baker_param :=
{|
  show p := "params{" ++ 
    "baker: " ++ show p.(baker) ++ sep ++
    "freeze: " ++ show p.(freezeBaker_) ++ "}"
|}.

Instance showTokenToTokenParam : Show token_to_token_param :=
{|
  show p := "params{" ++ 
    "exchange address: " ++ show p.(outputDexterContract) ++ sep ++
    "to: " ++ show p.(to_) ++ sep ++
    "min tokens bought: " ++ show p.(minTokensBought_) ++ sep ++
    "tokens sold: " ++ show p.(tokensSold_) ++ sep ++
    "deadline: " ++ show p.(ttt_deadline) ++ "}"
|}.

Instance showCPMMDexterMsg : Show DexterMsg :=
{|
  show m :=
    match m with
    | AddLiquidity param => "add_liquidity " ++ show param
    | RemoveLiquidity param => "remove_liquidity " ++ show param
    | XtzToToken param => "xtz_to_token " ++ show param
    | TokenToXtz param => "token_to_xtz " ++ show param
    | SetBaker param => "set_baker " ++ show param
    | SetManager addr => "set_manager " ++ show addr
    | SetLqtAddress addr => "set_lqt_address " ++ show addr
    | UpdateTokenPool => "update_token_pool"
    | TokenToToken param => "token_to_token " ++ show param
    end
|}.

Instance showCPMMMsg : Show Dexter2CPMM.Msg :=
{|
  show m := show m
|}.

Instance showCPMMSetup : Show Dexter2CPMM.Setup :=
{|
  show p := "Setup{" ++ 
    "lqt total: " ++ show p.(lqtTotal_) ++ sep ++
    "manager: " ++ show p.(manager_) ++ sep ++
    "token address: " ++ show p.(tokenAddress_) ++ sep ++
    "token Id: " ++ show p.(tokenId_) ++ "}"
|}.

Instance showCPMMState : Show Dexter2CPMM.State :=
{|
  show p := "State{" ++ 
    "token pool: " ++ show p.(tokenPool) ++ sep ++
    "xtz pool: " ++ show p.(xtzPool) ++ sep ++
    "lqt pool: " ++ show p.(lqtTotal) ++ sep ++
    "is updating token pool: " ++ show p.(selfIsUpdatingTokenPool) ++ sep ++
    "baker frozen: " ++ show p.(freezeBaker) ++ sep ++
    "manager: " ++ show p.(manager) ++ sep ++
    "token address: " ++ show p.(tokenAddress) ++ sep ++
    "lqt address: " ++ show p.(lqtAddress) ++ sep ++
    "token Id: " ++ show p.(tokenId) ++ "}"
|}.

(** * Dexter2 Lqt Token printers *)
Instance showLqtSetup : Show Dexter2FA12.Setup :=
{|
  show p := "Setup{" ++ 
    "admin: " ++ show p.(admin_) ++ sep ++
    "lqt provider: " ++ show p.(lqt_provider) ++ sep ++
    "initial pool: " ++ show p.(initial_pool) ++ "}"
|}.

Instance showLqtState : Show Dexter2FA12.State :=
{|
  show p := "State{" ++ 
    "tokens: " ++ show p.(tokens) ++ sep ++
    "allowances: " ++ show p.(allowances) ++ sep ++
    "total supply: " ++ show p.(total_supply) ++ sep ++
    "admin: " ++ show p.(admin) ++ "}"
|}.

Instance showTransferParam : Show transfer_param :=
{|
  show p := "params{" ++ 
    "from: " ++ show p.(from) ++ sep ++
    "to: " ++ show p.(to) ++ sep ++
    "value: " ++ show p.(value) ++ "}"
|}.

Instance showApproveParam : Show approve_param :=
{|
  show p := "params{" ++ 
    "spender: " ++ show p.(spender) ++ sep ++
    "value: " ++ show p.(value_) ++ "}"
|}.

Instance showMintOrBurnParam : Show mintOrBurn_param :=
{|
  show p := "params{" ++ 
    "quantity: " ++ show p.(quantity) ++ sep ++
    "target: " ++ show p.(target) ++ "}"
|}.

Instance showGetAllowanceParam : Show getAllowance_param :=
{|
  show p := "params{" ++ 
    "request: " ++ show p.(request) ++ sep ++
    "callback addr: " ++ show p.(allowance_callback).(return_addr) ++ "}"
|}.

Instance showGetBalanceParam : Show getBalance_param :=
{|
  show p := "params{" ++ 
    "owner: " ++ show p.(owner_) ++ sep ++
    "callback addr: " ++ show p.(balance_callback).(return_addr) ++ "}"
|}.

Instance showGetTotalSupplyParam : Show getTotalSupply_param :=
{|
  show p := "params{" ++ 
    "callback addr: " ++ show p.(supply_callback).(return_addr) ++ "}"
|}.

Instance showLqtMsg : Show Dexter2FA12.Msg :=
{|
  show m :=
    match m with
    | msg_transfer param => "transfer " ++ show param
    | msg_approve param => "approve " ++ show param
    | msg_mint_or_burn param => "mint_or_burn " ++ show param
    | msg_get_allowance param => "get_allowance " ++ show param
    | msg_get_balance param => "get_balance " ++ show param
    | msg_get_total_supply param => "get_total_supply " ++ show param
    end
|}.

(** * Combined message printer *)
Instance showSerializedMsg : Show SerializedValue :=
  Derive Show Msg <
    FA2Token.Msg,
    Dexter2CPMM.Msg,
    Dexter2FA12.Msg,
    FA2Token.Setup,
    Dexter2CPMM.Setup,
    Dexter2FA12.Setup >.

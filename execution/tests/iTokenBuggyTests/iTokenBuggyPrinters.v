From ConCert Require Import Blockchain.
From ConCert Require Import iTokenBuggy.
From ConCert.Execution.QCTests Require Import TestUtils.
From QuickChick Require Import QuickChick.

Section iTokenBuggyPrinters.
Context `{Show Address}.
Local Open Scope string_scope.


Instance showMsg : Show Msg :=
{|
  show m := match m with
            | transfer_from from to amount =>
              "transfer_from " ++ show from ++ " " ++ show to ++ " " ++ show amount
            | approve delegate amount => "approve " ++ show delegate ++ " " ++ show amount
            | mint amount => "mint " ++ show amount
            | burn amount => "burn " ++ show amount
            end
|}.

Instance showTokenSetup : Show Setup :=
{|
  show setup := "Setup{owner: " ++ show setup.(owner) ++ sep ++ "init_amount: " ++ show setup.(init_amount) ++ "}"
|}.

Instance showTokenState : Show iTokenBuggy.State :=
{|
  show s := "State{total_supply: " ++ show s.(total_supply) ++ sep
               ++ "balances: " ++ show s.(balances) ++ sep
               ++ "allowances: " ++ show s.(allowances) ++ "}"
|}.

End iTokenBuggyPrinters.
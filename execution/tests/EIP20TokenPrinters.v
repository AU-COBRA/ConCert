From ConCert Require Import Blockchain LocalBlockchain.
From ConCert Require Import EIP20Token.
From ConCert Require Import Serializable.
From ConCert Require Import BoundedN ChainedList.
From ConCert.Execution.QCTests Require Import ChainGens TestUtils ChainPrinters.

Require Import ZArith Strings.Ascii Strings.String.

From QuickChick Require Import QuickChick. Import QcNotation.
From ExtLib.Structures Require Import Functor Applicative.
Require Export ExtLib.Structures.Monads.
Export MonadNotation. Open Scope monad_scope.
From Coq Require Import List. Import ListNotations.
From Coq Require Import Strings.BinaryString.
From Coq Require Import Morphisms.
From Coq Require Import Program.Basics.
Require Import Containers.
Notation "f 'o' g" := (compose f g) (at level 50).
Open Scope string_scope.

Arguments SerializedValue : clear implicits.
Arguments deserialize : clear implicits.
Arguments serialize : clear implicits.

Let AddrSize := (2^8)%N.
Instance BaseTypes : ChainBase := LocalChainBase.

Local Open Scope string_scope.

Instance showTokenValue : Show TokenValue :=
{|
	show v := show v
|}.

Instance showMsg : Show Msg :=
{|
	show m := match m with
						| transfer to amount => "transfer " ++ show to ++ " " ++ show amount
						| transfer_from from to amount => 
							"transfer_from " ++ show from ++ " " ++ show to ++ " " ++ show amount 
						| approve delegate amount => "approve " ++ show delegate ++ " " ++ show amount
						end
|}.

Instance showTokenSetup : Show Setup :=
{|
	show setup := "Setup{owner: " ++ show setup.(owner) ++ sep ++ "init_amount: " ++ show setup.(init_amount) ++ "}"
|}.

Instance showTokenState : Show EIP20Token.State :=
{|
	show s := "State{total_supply: " ++ show s.(total_supply) ++ sep
							 ++ "balances: " ++ show s.(balances) ++ sep
							 ++ "allowances: " ++ show s.(allowances) ++ "}"
|}.
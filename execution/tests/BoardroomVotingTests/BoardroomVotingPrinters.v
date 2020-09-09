From ConCert Require Import Blockchain.
From ConCert Require Import BoardroomVoting.
From ConCert.Execution.QCTests Require Import TestUtils.
From QuickChick Require Import QuickChick.
From Coq Require Import ZArith.

Section BoardroomPrinters.
Context `{Show Address}.
Local Open Scope string_scope.

Derive Show for BinNums.positive.
Derive Show for Msg.

Instance showBoardroomVotingSetup : Show Setup :=
{|
  show setup := "Setup{" ++
                  "eligible_voters: " ++ show setup.(eligible_voters) ++ sep ++
                  "finish_registration_by: " ++ show setup.(finish_registration_by) ++ sep ++
                  "finish_commit_by: " ++ show setup.(finish_commit_by) ++ sep ++
                  "finish_vote_by: " ++ show setup.(finish_vote_by) ++ sep ++
                  "registration_deposit: " ++ show setup.(registration_deposit) ++ sep ++ "}"
|}.

Instance showVoterInfo : Show VoterInfo :=
{|
  show info := "VoterInfo{" ++ 
  "voter_index: " ++ show info.(voter_index) ++ sep ++  
  "vote_hash: " ++ show info.(vote_hash) ++ sep ++
  "public_vote: " ++ show info.(public_vote) ++ sep ++ "}"
|}.

Instance showBoardroomVotingState : Show BoardroomVoting.State :=
{|
  show s := "BoardroomVotingState{" ++
              "owner: " ++ show s.(owner) ++ sep ++ 
              "registered_voters: " ++ show s.(registered_voters) ++ sep ++
              "public_keys: " ++ show s.(public_keys) ++ sep ++
              "setup: " ++ show s.(setup) ++ sep ++ 
              "tally: " ++ show s.(tally) ++ sep ++ "}"
|}.

End BoardroomPrinters.
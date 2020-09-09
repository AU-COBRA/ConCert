From ConCert Require Import Blockchain BoardroomVoting.
From ConCert Require Import Serializable.
From ConCert.Execution.QCTests Require Import TestUtils TraceGens.
From Coq Require Import Int63.
Require Import ZArith.

From QuickChick Require Import QuickChick. Import QcNotation.
From ExtLib.Structures Require Import Monads.
Import MonadNotation. Open Scope monad_scope.
From Coq Require Import List. Import ListNotations.
Require Import Containers.

Module Type BoardroomVotingGensInfo.
  Parameter contract_addr : Address.
  Parameter hash_func : list positive -> positive.
                                  (* public, private, reconstructed key *)
  Parameter voters : FMap Address (Z * Z * Z).
  Parameter voters_signup : FMap Address ((list positive -> positive) -> @Msg Z).
  Parameter gAccount : G Address.
  Parameter gAccountWithout : list Address -> GOpt Address.
End BoardroomVotingGensInfo.

Module BoardroomVotingGens (Info : BoardroomVotingGensInfo).
Import Info.

Definition Env := Environment.
Open Scope Z_scope.

(* Definition gAccountWithBalance (e : Env) (gAccOpt : GOpt Address) : GOpt (Address * Amount) :=
  addr <- suchThatMaybeOpt gAccOpt (fun addr => 0 <? e.(account_balance) addr) ;;
  returnGenSome (addr, e.(account_balance) addr). *)
(* Close Scope Z_scope. *)

Definition liftOptGen {A : Type} (g : G A) : G (option A) :=
  a <- g ;;
  returnGen (Some a).

Derive Arbitrary for positive.
(* Derive Arbitrary for BoardroomVoting.Msg. *)
(* Definition gMsg : G BoardroomVoting.Msg := arbitrary. *)


Definition gBoardroomVotingMsg : G (option Action) :=
  let call caller m := returnGenSome ( 
    build_act caller (act_call contract_addr 0 (@serialize BoardroomVoting.Msg _ m))) in
  (* state <- returnGen (get_contract_state BoardroomVoting.State env contract_addr) ;; *)
  backtrack [
    (* 
    | signup (pk : A) (proof : A * Z)
    | commit_to_vote (hash : positive)
    | submit_vote (v : A) (proof : VoteProof)
    | tally_votes.
    *)
    (1%nat, '(voter, _) <- sampleFMapOpt voters ;; 
            match FMap.find voter voters_signup with
            | Some h => let msg : Msg := h hash_func in
                        call voter msg
            | None => returnGen None
            end
    )
  ].

Close Scope Z_scope.

Definition gBoardroomVotingTrace cb length :=
  let max_act_depth := 1 in
  let max_acts_per_block := 1 in
  gChain cb (fun e _ => gBoardroomVotingMsg ) length max_act_depth max_acts_per_block.

Instance showInt63 : Show Int63.int :=
{|
  show i := show (to_Z i)
|}.
Instance gensizedInt63 : GenSized Int63.int :=
{|
  arbitrarySized n := liftM of_Z (arbitrarySized n)
|}.
Instance shrinkInt63 : Shrink Int63.int :=
{|
  shrink n := [n]
|}.

End BoardroomVotingGens.

Module DummyTestInfo <: BoardroomVotingGensInfo.
  Definition hash_func (l : list positive) : positive := xH.
                                  (* public, private, reconstructed key *)
  Definition voters : FMap Address (Z * Z * Z) := FMap.empty.
  
  Definition voters_signup : FMap Address ((list positive -> positive) -> @Msg Z) := FMap.empty.
  Definition contract_addr := zero_address.
  Definition gAccount := returnGen zero_address.
  Definition gAccountWithout (ws : list Address) := returnGenSome zero_address.
End DummyTestInfo.
Module MG := BoardroomVotingGens.BoardroomVotingGens DummyTestInfo. Import MG.
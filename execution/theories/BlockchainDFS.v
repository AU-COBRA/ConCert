From ConCert.Execution Require Import BlockchainBase.
From ConCert.Execution Require Import ChainedList.
From Stdlib Require Import Permutation.
From Stdlib Require Import List.
Import ListNotations.



Section BreadthFirst.
  Context `{Base : ChainBase}.

  Definition chainstep_states {prev_bstate next_bstate} (step : ChainStep prev_bstate next_bstate) :=
    (prev_bstate, next_bstate).

  Fixpoint BFSPermutations {from to : ChainState} (trace : ChainTrace from to) : Prop :=
    match trace with
    | clnil => True
    | snoc trace' step =>
      match trace' with
      | clnil =>
        match step with
        | step_permute _ _ _ _ => False
        | _ => True
        end
      | snoc trace'' (step_action _ _ _ acts new_acts _ _ _) =>
        match step with
        | step_permute _ _ _ _ =>
          (chain_state_queue to) = (acts ++ new_acts) /\
          BFSPermutations trace'
        | _ => BFSPermutations trace'
        end
      | _ => BFSPermutations trace'
      end
    end.

  Definition BFSChainTrace {from to : ChainState} :=
    {x : ChainTrace from to | BFSPermutations x}.

  Definition BFSChainTrace_to_ChainTrace {from to : ChainState}
                                         (trace : @BFSChainTrace from to)
                                         : ChainTrace from to :=
    proj1_sig trace.

End BreadthFirst.

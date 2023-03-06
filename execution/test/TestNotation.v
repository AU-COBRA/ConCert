From ConCert.Execution Require Import Blockchain.
From ConCert.Execution.Test Require Import TraceGens.
From ConCert.Execution.Test Require Import TestUtils.
From QuickChick Require Import QuickChick.
From Coq Require Import List.
From Coq Require Import ZArith.
From Coq Require Import Bool.

(** * Test parameters *)
(** These determine the behaviour of the chain trace generators.
    The following parameters are available.
    - max_trace_length: This determines the maximum number of blocks that
      will be added to the trace by the generator. Default value is 7.
    - max_acts_per_block: Defines the maximum number of actions that the
      generator will add per block. Default value is 2.
    - act_depth
    - DepthFirst: A boolean value denoting whether actions are executed in
      a depth first order (true) or breadth first order (false).
      Default value is true.
    - AddrSize: The total number of valid addresses in the blockchain.
      The first half of the address space is reserved
      for user accounts while the second half is reserved for smart contracts.
      Default value is 256 (overwriting this value is not recommended).
    - BlockReward: The reward given to the address adding a block to the chain.
      Default value is 50.
    - BlockCreator: The address used when adding new blocks to the chain.
      Default value is "creator" (address 10).
    - MaxGenAttempts: The maximum attempts at generating a valid action in a block.
      If the maximum number of attempts is exceeded the generator will proceed to the
      next block. This value should be kept low as it has a high impact on performance
      of trace generation. Default value is 2.

    These values can be overwritten between tests by:
    << Extract Constant max_trace_length => "3" >>
*)
Definition max_trace_length : nat := 7.
Definition max_acts_per_block : nat := 2.
Definition act_depth : nat := 3.

Declare Scope qc_test_scope.

Module Type TestNotationParameters.
  Parameter gAction : (Environment -> GOpt Action).
  Parameter init_cb : ChainBuilder.
End TestNotationParameters.

Module TestNotations (p : TestNotationParameters).
  Import p.

  Definition gChain_ init_cb max_trace_length :=
    gChain init_cb
      (fun env act_depth => gAction env) max_trace_length act_depth max_acts_per_block.

  Definition gChain :=
    gChain init_cb
      (fun env act_depth => gAction env) max_trace_length act_depth max_acts_per_block.

  Definition gInvalidActions g :=
    gInvalidAction init_cb
      (fun env act_depth => g env) max_trace_length 1 1.

  Definition forAllInvalidActions `{Show ChainBuilder} `{Show Action} g P :=
    forAll (gInvalidActions g)
      (fun '(cb, acts) => if length acts =? 0
                          then checker true
                          else disjoin (map (fun act => P cb act) acts)).

  Definition forAllChainBuilders `{Show ChainBuilder} :=
    forAllChainBuilder max_trace_length init_cb gChain_.

  Definition forAllBlocks `{Show ChainState} `{Show ChainBuilder} :=
    forAllBlocks max_trace_length init_cb gChain_.

  Definition forAllChainStatePairs `{Show ChainBuilder} :=
    forAllChainStatePairs max_trace_length init_cb gChain_.

  Definition bool_to_option {A} (P : A -> bool) : (A -> option unit) :=
    fun cs => if P cs then Some tt else None.

  Definition checkForAllStatesInTrace {A} Q :=
    fun (_ : A) (pre_trace post_trace : list ChainState) =>
      checker (fold_left (fun a (cs : ChainState) => a && (Q pre_trace cs)) post_trace true).

  Notation "cb '~~>' pf" :=
    (reachableFrom_chaintrace cb gChain_ pf)
    (at level 45, left associativity) : qc_test_scope.
  Notation "lc '~~~>' pf1 '===>' pf2" :=
    (reachableFrom_implies_chaintracePropSized max_trace_length lc gChain_ pf1 pf2)
    (at level 45, pf1 at next level, left associativity) : qc_test_scope.
  Notation "'{{' P '}}'" :=
    (forAllChainState max_trace_length init_cb gChain_ P)
    (at level 60, no associativity) : qc_test_scope.
  Notation "'{{' P '}}' '==>' '{{' Q '}}'" :=
    (forAllChainState_implication max_trace_length init_cb gChain_ P Q)
    (at level 60, left associativity) : qc_test_scope.
  Notation "'{{' P '}}' c '{{' Q '}}'" :=
    (pre_post_assertion max_trace_length init_cb gChain_ c P Q)
    (at level 60, c at next level, no associativity) : qc_test_scope.
  Notation "'{{' P '}}' c '{{' Q '}}' chain" :=
    (pre_post_assertion max_trace_length chain gChain_ c P Q)
    (at level 60, c at next level, chain at next level, no associativity) : qc_test_scope.
End TestNotations.
Open Scope qc_test_scope.

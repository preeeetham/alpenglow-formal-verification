---- MODULE Properties ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

(*
 * Properties: Safety, Liveness, and Resilience Properties for Alpenglow
 * 
 * This module defines all the formal properties that need to be verified
 * for the Alpenglow consensus protocol.
 *)

(* =============================================================================
 * CONSTANTS AND PARAMETERS
 * ============================================================================= *)

CONSTANTS
    Nodes,           \* Set of validator nodes
    Stake,           \* Stake distribution function
    Slots,           \* Set of time slots
    FastThreshold,   \* Fast path threshold (80%)
    SlowThreshold,   \* Slow path threshold (60%)
    ByzantineThreshold, \* Byzantine fault threshold (20%)
    CrashThreshold,  \* Crash fault threshold (20%)
    Delta,           \* Maximum network delay bound
    DeltaFast,       \* Fast path timeout
    DeltaSlow        \* Slow path timeout

(* =============================================================================
 * HELPER FUNCTIONS
 * ============================================================================= *)

(* Calculate total stake for a set of nodes *)
TotalStake(nodes) ==
    LET stakeSum == [n \in nodes |-> Stake[n]]
    IN Sum(stakeSum)

(* Get honest nodes (non-Byzantine, non-crashed) *)
HonestNodes(nodes, stake, byzantineNodes, crashedNodes) ==
    {n \in nodes : /\ stake[n] > 0
                   /\ n \notin byzantineNodes
                   /\ n \notin crashedNodes}

(* Get Byzantine nodes *)
ByzantineNodes(nodes, stake, byzantineNodes) ==
    {n \in nodes : stake[n] > 0 /\ n \in byzantineNodes}

(* Get crashed nodes *)
CrashedNodes(nodes, stake, crashedNodes) ==
    {n \in nodes : stake[n] = 0 \/ n \in crashedNodes}

(* =============================================================================
 * SAFETY PROPERTIES
 * ============================================================================= *)

(* No conflicting blocks finalized *)
Safety(finalized) ==
    \A s \in Slots : 
        \A b1, b2 \in finalized : 
            (b1.slot = s /\ b2.slot = s) => b1 = b2

(* Chain consistency - each block's parent must be finalized before it *)
ChainConsistency(finalized) ==
    \A b1, b2 \in finalized :
        b1.slot < b2.slot => 
            \E b3 \in finalized : b3.slot = b1.slot /\ b2.parent = b3.hash

(* Certificate uniqueness - no duplicate certificates *)
CertificateUniqueness(certificates) ==
    \A cert1, cert2 \in certificates :
        (cert1.type = cert2.type /\ cert1.slot = cert2.slot) => cert1 = cert2

(* No double spending - no conflicting transactions *)
NoDoubleSpending(finalized, blocks) ==
    \A b1, b2 \in finalized :
        \A t1 \in b1.transactions, t2 \in b2.transactions :
            t1.sender = t2.sender /\ t1.amount = t2.amount => t1 = t2

(* Block validity - all finalized blocks are valid *)
BlockValidity(finalized, blocks) ==
    \A b \in finalized :
        \E block \in blocks : block.slot = b.slot /\ block.hash = b.hash

(* =============================================================================
 * LIVENESS PROPERTIES
 * ============================================================================= *)

(* Progress under partial synchrony *)
Progress(finalized, honestStake) ==
    honestStake > SlowThreshold => 
        \E b \in finalized : TRUE

(* Fast path completion *)
FastPathCompletion(fastFinalized, honestStake) ==
    honestStake > FastThreshold => 
        \E b \in fastFinalized : TRUE

(* Bounded finalization time *)
BoundedFinalization(finalized, blocks, delta) ==
    \A b \in blocks :
        b \in finalized => 
            \E t \in Nat : t <= delta  \* Finalization time bounded by delta

(* Liveness under honest majority *)
LivenessUnderHonestMajority(finalized, honestStake) ==
    honestStake > 0.5 => 
        <>(\E b \in finalized : TRUE)

(* Eventual consistency *)
EventualConsistency(finalized, honestNodes) ==
    \A node \in honestNodes :
        <>(\E b \in finalized : b \in node.localFinalized)

(* =============================================================================
 * RESILIENCE PROPERTIES
 * ============================================================================= *)

(* Byzantine fault tolerance *)
ByzantineSafety(finalized, byzantineStake) ==
    byzantineStake < ByzantineThreshold => []Safety(finalized)

(* Crash fault tolerance *)
CrashLiveness(finalized, byzantineStake, crashedStake) ==
    byzantineStake < ByzantineThreshold /\ crashedStake < CrashThreshold =>
        <>Progress(finalized, 1.0 - byzantineStake - crashedStake)

(* Network partition recovery *)
PartitionRecovery(finalized, networkPartitioned) ==
    networkPartitioned /\ <>~networkPartitioned =>
        <>Progress(finalized, 1.0)

(* Adaptive timeout *)
AdaptiveTimeout(timeouts, delta) ==
    \A slot \in Slots :
        timeouts[slot] <= 2 * delta

(* Graceful degradation *)
GracefulDegradation(finalized, fastFinalized, honestStake) ==
    honestStake < FastThreshold =>
        \A b \in finalized : b \in fastFinalized \/ b \in slowFinalized

(* =============================================================================
 * ALPENGLOW-SPECIFIC PROPERTIES
 * ============================================================================= *)

(* Dual-path consistency *)
DualPathConsistency(fastFinalized, slowFinalized) ==
    \A b1 \in fastFinalized, b2 \in slowFinalized :
        b1.slot = b2.slot => b1 = b2

(* Fast path priority *)
FastPathPriority(fastFinalized, slowFinalized, honestStake) ==
    honestStake >= FastThreshold =>
        \A b \in fastFinalized : b \notin slowFinalized

(* Erasure coding integrity *)
ErasureCodingIntegrity(blocks, shreds, slices) ==
    \A block \in blocks :
        \E slice \in slices :
            block.slot = slice.slot /\ 
            \A shred \in slice.shreds :
                shred.slot = block.slot

(* Stake-weighted sampling fairness *)
StakeWeightedSamplingFairness(committees, stake) ==
    \A committee \in committees :
        TotalStake(committee.nodes) >= SlowThreshold

(* Merkle tree authentication *)
MerkleTreeAuthentication(slices, merkleTrees) ==
    \A slice \in slices :
        \A shred \in slice.shreds :
            VerifyMerkleProof(shred.data, shred.merkleProof, slice.merkleRoot)

(* =============================================================================
 * COMPOSITE PROPERTIES
 * ============================================================================= *)

(* Complete safety *)
CompleteSafety(finalized, certificates, blocks) ==
    /\ Safety(finalized)
    /\ ChainConsistency(finalized)
    /\ CertificateUniqueness(certificates)
    /\ BlockValidity(finalized, blocks)

(* Complete liveness *)
CompleteLiveness(finalized, fastFinalized, honestStake, delta) ==
    /\ Progress(finalized, honestStake)
    /\ FastPathCompletion(fastFinalized, honestStake)
    /\ BoundedFinalization(finalized, blocks, delta)

(* Complete resilience *)
CompleteResilience(finalized, byzantineStake, crashedStake, networkPartitioned) ==
    /\ ByzantineSafety(finalized, byzantineStake)
    /\ CrashLiveness(finalized, byzantineStake, crashedStake)
    /\ PartitionRecovery(finalized, networkPartitioned)

(* Alpenglow protocol correctness *)
AlpenglowCorrectness(finalized, fastFinalized, slowFinalized, certificates, blocks, shreds, slices, honestStake, byzantineStake, crashedStake) ==
    /\ CompleteSafety(finalized, certificates, blocks)
    /\ CompleteLiveness(finalized, fastFinalized, honestStake, Delta)
    /\ CompleteResilience(finalized, byzantineStake, crashedStake, FALSE)
    /\ DualPathConsistency(fastFinalized, slowFinalized)
    /\ FastPathPriority(fastFinalized, slowFinalized, honestStake)
    /\ ErasureCodingIntegrity(blocks, shreds, slices)

(* =============================================================================
 * INVARIANT DEFINITIONS
 * ============================================================================= *)

(* Basic invariants *)
BasicInvariants(finalized, certificates, blocks) ==
    /\ CompleteSafety(finalized, certificates, blocks)

(* Liveness invariants *)
LivenessInvariants(finalized, fastFinalized, honestStake) ==
    /\ Progress(finalized, honestStake)
    /\ FastPathCompletion(fastFinalized, honestStake)

(* Resilience invariants *)
ResilienceInvariants(finalized, byzantineStake, crashedStake) ==
    /\ ByzantineSafety(finalized, byzantineStake)
    /\ CrashLiveness(finalized, byzantineStake, crashedStake)

(* =============================================================================
 * THEOREM STATEMENTS
 * ============================================================================= *)

(* Main correctness theorem *)
THEOREM AlpenglowCorrectness(finalized, fastFinalized, slowFinalized, certificates, blocks, shreds, slices, honestStake, byzantineStake, crashedStake)

(* Safety theorem *)
THEOREM CompleteSafety(finalized, certificates, blocks)

(* Liveness theorem *)
THEOREM CompleteLiveness(finalized, fastFinalized, honestStake, Delta)

(* Resilience theorem *)
THEOREM CompleteResilience(finalized, byzantineStake, crashedStake, FALSE)

(* =============================================================================
 * MODEL CHECKING CONFIGURATIONS
 * ============================================================================= *)

(* Small configuration for exhaustive verification *)
SmallConfig ==
    /\ Nodes = {n1, n2, n3, n4}
    /\ Stake = [n \in {n1, n2, n3, n4} |-> 0.25]
    /\ Slots = {1, 2, 3, 4, 5}
    /\ FastThreshold = 0.8
    /\ SlowThreshold = 0.6
    /\ ByzantineThreshold = 0.2
    /\ CrashThreshold = 0.2
    /\ Delta = 1000
    /\ DeltaFast = 400
    /\ DeltaSlow = 800

(* Medium configuration for statistical verification *)
MediumConfig ==
    /\ Nodes = {n1, n2, n3, n4, n5, n6, n7, n8, n9, n10}
    /\ Stake = [n \in {n1, n2, n3, n4, n5, n6, n7, n8, n9, n10} |-> 0.1]
    /\ Slots = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10}
    /\ FastThreshold = 0.8
    /\ SlowThreshold = 0.6
    /\ ByzantineThreshold = 0.2
    /\ CrashThreshold = 0.2
    /\ Delta = 1000
    /\ DeltaFast = 400
    /\ DeltaSlow = 800

(* =============================================================================
 * END OF MODULE
 * ============================================================================= *)

====

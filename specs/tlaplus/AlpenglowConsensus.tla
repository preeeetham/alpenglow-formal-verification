---- MODULE AlpenglowConsensus ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

(*
 * Alpenglow Consensus Protocol Formal Specification
 * 
 * This module specifies the core Alpenglow consensus protocol with:
 * - Votor: Dual-path voting (fast 80%, slow 60%)
 * - Rotor: Erasure-coded block distribution
 * - Safety, Liveness, and Resilience properties
 *)

(* =============================================================================
 * CONSTANTS AND PARAMETERS
 * ============================================================================= *)

CONSTANTS
    Nodes,           \* Set of validator nodes
    MaxNodes,        \* Maximum number of nodes (2000)
    Stake,           \* Stake distribution function: Nodes -> [0,1]
    Slots,           \* Set of time slots
    Leaders,         \* Leader schedule: Slots -> Nodes
    BlockTime,       \* Block time parameter (400ms)
    Delta,           \* Maximum network delay bound
    Gamma,           \* Data shreds per slice (32)
    BigGamma,        \* Total shreds per slice (64)
    Kappa,           \* Data expansion ratio (Gamma/BigGamma = 2)
    W,               \* Blocks per leader window (4)
    ByzantineThreshold, \* Byzantine fault threshold (20%)
    CrashThreshold,  \* Crash fault threshold (20%)

(* =============================================================================
 * TYPE DEFINITIONS
 * ============================================================================= *)

VARIABLES
    nodes,           \* Set of active nodes
    stake,           \* Current stake distribution
    slots,           \* Set of processed slots
    leaders,         \* Current leader schedule
    blocks,          \* Proposed blocks
    votes,           \* Vote pool
    certificates,    \* Certificate store
    network,         \* Network state
    finalized,       \* Finalized blocks
    fastFinalized,   \* Fast-path finalized blocks
    notarized,       \* Notarized blocks
    skipped,         \* Skipped slots

(* =============================================================================
 * TYPE INVARIANTS
 * ============================================================================= *)

TypeOK ==
    /\ nodes \subseteq Nodes
    /\ stake \in [Nodes -> [0,1]]
    /\ slots \subseteq Slots
    /\ leaders \in [Slots -> Nodes]
    /\ blocks \subseteq [slot: Slots, hash: STRING, parent: STRING, data: STRING]
    /\ votes \subseteq [node: Nodes, slot: Slots, type: {"NotarVote", "NotarFallbackVote", "SkipVote", "SkipFallbackVote", "FinalVote"}, hash: STRING]
    /\ certificates \subseteq [type: {"FastFinalization", "Notarization", "NotarFallback", "Skip", "Finalization"}, slot: Slots, hash: STRING, stake: [0,1]]
    /\ network \in [Nodes -> [Nodes -> [message: STRING, timestamp: Nat]]]
    /\ finalized \subseteq [slot: Slots, hash: STRING]
    /\ fastFinalized \subseteq [slot: Slots, hash: STRING]
    /\ notarized \subseteq [slot: Slots, hash: STRING]
    /\ skipped \subseteq Slots

(* =============================================================================
 * HELPER FUNCTIONS
 * ============================================================================= *)

(* Calculate total stake for a set of nodes *)
TotalStake(nodes) ==
    LET stakeSum == [n \in nodes |-> stake[n]]
    IN Sum(stakeSum)

(* Check if a set of nodes has sufficient stake *)
HasSufficientStake(nodes, threshold) ==
    TotalStake(nodes) >= threshold

(* Get honest nodes (non-Byzantine, non-crashed) *)
HonestNodes ==
    {n \in nodes : /\ stake[n] > 0
                   /\ \A m \in nodes : network[n][m] = {}}

(* Get Byzantine nodes *)
ByzantineNodes ==
    {n \in nodes : stake[n] > 0 /\ n \notin HonestNodes}

(* Get crashed nodes *)
CrashedNodes ==
    {n \in nodes : stake[n] = 0}

(* Check if a block is valid *)
IsValidBlock(block) ==
    /\ block.slot \in Slots
    /\ block.hash \in STRING
    /\ block.parent \in STRING
    /\ block.data \in STRING

(* Check if a vote is valid *)
IsValidVote(vote) ==
    /\ vote.node \in nodes
    /\ vote.slot \in Slots
    /\ vote.type \in {"NotarVote", "NotarFallbackVote", "SkipVote", "SkipFallbackVote", "FinalVote"}
    /\ vote.hash \in STRING

(* =============================================================================
 * VOTOR SPECIFICATION
 * ============================================================================= *)

(* Generate a vote *)
GenerateVote(node, slot, voteType, hash) ==
    /\ node \in nodes
    /\ slot \in Slots
    /\ voteType \in {"NotarVote", "NotarFallbackVote", "SkipVote", "SkipFallbackVote", "FinalVote"}
    /\ hash \in STRING
    /\ votes' = votes \cup {[node |-> node, slot |-> slot, type |-> voteType, hash |-> hash]}
    /\ UNCHANGED <<stake, slots, leaders, blocks, certificates, network, finalized, fastFinalized, notarized, skipped>>

(* Aggregate votes into certificates *)
AggregateVotes(slot, voteType) ==
    LET relevantVotes == {v \in votes : v.slot = slot /\ v.type = voteType}
        votingNodes == {v.node : v \in relevantVotes}
        totalVotingStake == TotalStake(votingNodes)
    IN /\ totalVotingStake >= 0.6  \* 60% threshold for most certificates
       /\ certificates' = certificates \union {[type |-> voteType, slot |-> slot, hash |-> "aggregated", stake |-> totalVotingStake]}
       /\ UNCHANGED <<stake, slots, leaders, blocks, votes, network, finalized, fastFinalized, notarized, skipped>>

(* Fast path finalization (80% threshold) *)
FastPathFinalization(slot, hash) ==
    LET notarVotes == {v \in votes : v.slot = slot /\ v.type = "NotarVote" /\ v.hash = hash}
        votingNodes == {v.node : v \in notarVotes}
        totalVotingStake == TotalStake(votingNodes)
    IN /\ totalVotingStake >= 0.8  \* 80% threshold for fast path
       /\ fastFinalized' = fastFinalized \union {[slot |-> slot, hash |-> hash]}
       /\ finalized' = finalized \union {[slot |-> slot, hash |-> hash]}
       /\ certificates' = certificates \union {[type |-> "FastFinalization", slot |-> slot, hash |-> hash, stake |-> totalVotingStake]}
       /\ UNCHANGED <<stake, slots, leaders, blocks, votes, network, notarized, skipped>>

(* Slow path finalization (60% threshold) *)
SlowPathFinalization(slot, hash) ==
    LET notarVotes == {v \in votes : v.slot = slot /\ v.type = "NotarVote" /\ v.hash = hash}
        fallbackVotes == {v \in votes : v.slot = slot /\ v.type = "NotarFallbackVote" /\ v.hash = hash}
        allVotes == notarVotes \union fallbackVotes
        votingNodes == {v.node : v \in allVotes}
        totalVotingStake == TotalStake(votingNodes)
    IN /\ totalVotingStake >= 0.6  \* 60% threshold for slow path
       /\ notarized' = notarized \union {[slot |-> slot, hash |-> hash]}
       /\ certificates' = certificates \union {[type |-> "NotarFallback", slot |-> slot, hash |-> hash, stake |-> totalVotingStake]}
       /\ UNCHANGED <<stake, slots, leaders, blocks, votes, network, finalized, fastFinalized, skipped>>

(* =============================================================================
 * ROTOR SPECIFICATION
 * ============================================================================= *)

(* Erasure coding parameters *)
ErasureCodingParams ==
    /\ Gamma = 32
    /\ BigGamma = 64
    /\ Kappa = BigGamma / Gamma  \* = 2

(* Encode block into shreds *)
EncodeBlock(block) ==
    LET shreds == [i \in 1..BigGamma |-> [index |-> i, data |-> block.data, merkleRoot |-> "root"]]
    IN shreds

(* Decode shreds into block *)
DecodeShreds(shreds) ==
    LET dataShreds == {s \in shreds : s.index <= Gamma}
    IN IF Cardinality(dataShreds) >= Gamma
       THEN [slot |-> "decoded", hash |-> "decoded", parent |-> "decoded", data |-> "decoded"]
       ELSE [slot |-> "error", hash |-> "error", parent |-> "error", data |-> "error"]

(* Stake-weighted relay sampling (PS-P algorithm) *)
StakeWeightedSampling(committee, targetSize) ==
    LET weights == [n \in committee |-> stake[n]]
        totalWeight == Sum(weights)
        probabilities == [n \in committee |-> weights[n] / totalWeight]
    IN LET selected == {}
        IN selected  \* Simplified for now - would implement proper sampling

(* =============================================================================
 * STATE TRANSITIONS
 * ============================================================================= *)

(* Propose a new block *)
ProposeBlock(slot, hash, parent, data) ==
    /\ slot \in Slots
    /\ slot \notin DOMAIN blocks
    /\ hash \in STRING
    /\ parent \in STRING
    /\ data \in STRING
    /\ blocks' = blocks \union {[slot |-> slot, hash |-> hash, parent |-> parent, data |-> data]}
    /\ UNCHANGED <<stake, slots, leaders, votes, certificates, network, finalized, fastFinalized, notarized, skipped>>

(* Process a slot *)
ProcessSlot(slot) ==
    /\ slot \in Slots
    /\ slot \notin slots
    /\ slots' = slots \union {slot}
    /\ UNCHANGED <<stake, leaders, blocks, votes, certificates, network, finalized, fastFinalized, notarized, skipped>>

(* Network message delivery *)
DeliverMessage(from, to, message) ==
    /\ from \in nodes
    /\ to \in nodes
    /\ message \in STRING
    /\ network' = [n \in nodes |-> 
        IF n = to 
        THEN [m \in nodes |-> 
            IF m = from 
            THEN network[n][m] \union {[message |-> message, timestamp |-> 0]}
            ELSE network[n][m]]
        ELSE network[n]]
    /\ UNCHANGED <<stake, slots, leaders, blocks, votes, certificates, finalized, fastFinalized, notarized, skipped>>

(* =============================================================================
 * INITIAL STATE
 * ============================================================================= *)

Init ==
    /\ nodes = Nodes
    /\ stake = Stake
    /\ slots = {}
    /\ leaders = Leaders
    /\ blocks = {}
    /\ votes = {}
    /\ certificates = {}
    /\ network = [n \in Nodes |-> [m \in Nodes |-> {}]]
    /\ finalized = {}
    /\ fastFinalized = {}
    /\ notarized = {}
    /\ skipped = {}

(* =============================================================================
 * NEXT STATE RELATION
 * ============================================================================= *)

Next ==
    \/ \E slot \in Slots, hash \in STRING, parent \in STRING, data \in STRING :
        ProposeBlock(slot, hash, parent, data)
    \/ \E slot \in Slots :
        ProcessSlot(slot)
    \/ \E node \in Nodes, slot \in Slots, voteType \in {"NotarVote", "NotarFallbackVote", "SkipVote", "SkipFallbackVote", "FinalVote"}, hash \in STRING :
        GenerateVote(node, slot, voteType, hash)
    \/ \E slot \in Slots, voteType \in {"NotarVote", "NotarFallbackVote", "SkipVote", "SkipFallbackVote", "FinalVote"} :
        AggregateVotes(slot, voteType)
    \/ \E slot \in Slots, hash \in STRING :
        FastPathFinalization(slot, hash)
    \/ \E slot \in Slots, hash \in STRING :
        SlowPathFinalization(slot, hash)
    \/ \E from \in Nodes, to \in Nodes, message \in STRING :
        DeliverMessage(from, to, message)

(* =============================================================================
 * SPECIFICATION
 * ============================================================================= *)

Spec == Init /\ [][Next]_vars

(* =============================================================================
 * SAFETY PROPERTIES
 * ============================================================================= *)

(* No conflicting blocks finalized *)
Safety ==
    \A s \in Slots : 
        \A b1, b2 \in finalized : 
            (b1.slot = s /\ b2.slot = s) => b1 = b2

(* Chain consistency *)
ChainConsistency ==
    \A b1, b2 \in finalized :
        b1.slot <= b2.slot => b2.parent = b1.hash

(* Certificate uniqueness *)
CertificateUniqueness ==
    \A cert1, cert2 \in certificates :
        (cert1.type = cert2.type /\ cert1.slot = cert2.slot) => cert1 = cert2

(* =============================================================================
 * LIVENESS PROPERTIES
 * ============================================================================= *)

(* Progress under partial synchrony *)
Progress ==
    (TotalStake(HonestNodes) > 0.6) => 
        \E b \in blocks : b \in finalized

(* Fast path completion *)
FastPath ==
    (TotalStake(HonestNodes) > 0.8) => 
        \E b \in blocks : b \in fastFinalized

(* Bounded finalization time *)
BoundedFinalization ==
    \A b \in blocks :
        b \in finalized => TRUE  \* Simplified - would check timing constraints

(* =============================================================================
 * RESILIENCE PROPERTIES
 * ============================================================================= *)

(* Byzantine fault tolerance *)
ByzantineSafety ==
    (TotalStake(ByzantineNodes) < 0.2) => []Safety

(* Crash fault tolerance *)
CrashLiveness ==
    (TotalStake(ByzantineNodes) < 0.2 /\ TotalStake(CrashedNodes) < 0.2) =>
        <>Progress

(* Network partition recovery *)
PartitionRecovery ==
    TRUE  \* Simplified - would check network healing

(* =============================================================================
 * INVARIANTS
 * ============================================================================= *)

Invariants ==
    /\ TypeOK
    /\ Safety
    /\ ChainConsistency
    /\ CertificateUniqueness

(* =============================================================================
 * THEOREMS
 * ============================================================================= *)

THEOREM Spec => []Invariants

(* =============================================================================
 * MODEL CHECKING CONFIGURATION
 * ============================================================================= *)

(* Small configuration for exhaustive verification *)
SmallConfig ==
    /\ Nodes = {n1, n2, n3, n4}
    /\ MaxNodes = 4
    /\ Stake = [n \in Nodes |-> 0.25]  \* Equal stake distribution
    /\ Slots = {1, 2, 3, 4, 5}
    /\ Leaders = [s \in Slots |-> IF s <= 2 THEN n1 ELSE IF s <= 4 THEN n2 ELSE n3]
    /\ BlockTime = 400
    /\ Delta = 1000
    /\ Gamma = 32
    /\ BigGamma = 64
    /\ Kappa = 2
    /\ W = 4
    /\ ByzantineThreshold = 0.2
    /\ CrashThreshold = 0.2

(* =============================================================================
 * END OF MODULE
 * ============================================================================= *)

====

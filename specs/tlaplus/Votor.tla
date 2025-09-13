---- MODULE Votor ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

(*
 * Votor: Voting Component of Alpenglow Consensus
 * 
 * Implements dual-path voting:
 * - Fast path: Single round finalization with ≥80% stake participation
 * - Slow path: Two round finalization with ≥60% stake participation
 * - Concurrent execution with min(δ₈₀%, 2δ₆₀%) finalization time
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
    DeltaFast,       \* Fast path timeout
    DeltaSlow,       \* Slow path timeout
    LeaderWindow,    \* Blocks per leader window (4)

(* =============================================================================
 * VARIABLES
 * ============================================================================= *)

VARIABLES
    votes,           \* Vote pool
    certificates,    \* Certificate store
    fastFinalized,   \* Fast-path finalized blocks
    slowFinalized,   \* Slow-path finalized blocks
    notarized,       \* Notarized blocks
    skipped,         \* Skipped slots
    timeouts,        \* Timeout tracking
    safeToNotar,     \* SafeToNotar events
    safeToSkip,      \* SafeToSkip events

(* =============================================================================
 * TYPE DEFINITIONS
 * ============================================================================= *)

VoteType == {"NotarVote", "NotarFallbackVote", "SkipVote", "SkipFallbackVote", "FinalVote"}

CertificateType == {"FastFinalization", "Notarization", "NotarFallback", "Skip", "Finalization"}

Vote == [node: Nodes, slot: Slots, type: VoteType, hash: STRING, timestamp: Nat]

Certificate == [type: CertificateType, slot: Slots, hash: STRING, stake: [0,1], timestamp: Nat]

(* =============================================================================
 * TYPE INVARIANTS
 * ============================================================================= *)

TypeOK ==
    /\ votes \subseteq Vote
    /\ certificates \subseteq Certificate
    /\ fastFinalized \subseteq [slot: Slots, hash: STRING]
    /\ slowFinalized \subseteq [slot: Slots, hash: STRING]
    /\ notarized \subseteq [slot: Slots, hash: STRING]
    /\ skipped \subseteq Slots
    /\ timeouts \in [Slots -> Nat]
    /\ safeToNotar \subseteq Slots
    /\ safeToSkip \subseteq Slots

(* =============================================================================
 * HELPER FUNCTIONS
 * ============================================================================= *)

(* Calculate total stake for a set of nodes *)
TotalStake(nodes) ==
    LET stakeSum == [n \in nodes |-> Stake[n]]
    IN Sum(stakeSum)

(* Get votes of a specific type for a slot *)
GetVotes(slot, voteType) ==
    {v \in votes : v.slot = slot /\ v.type = voteType}

(* Get voting nodes for a specific vote type and slot *)
GetVotingNodes(slot, voteType) ==
    {v.node : v \in GetVotes(slot, voteType)}

(* Check if sufficient stake has voted *)
HasSufficientStake(slot, voteType, threshold) ==
    TotalStake(GetVotingNodes(slot, voteType)) >= threshold

(* Get all votes for a slot (any type) *)
GetAllVotes(slot) ==
    {v \in votes : v.slot = slot}

(* Check if a slot is safe to notarize *)
IsSafeToNotar(slot) ==
    LET notarVotes == GetVotes(slot, "NotarVote")
        fallbackVotes == GetVotes(slot, "NotarFallbackVote")
        allVotes == notarVotes \union fallbackVotes
        votingNodes == {v.node : v \in allVotes}
    IN TotalStake(votingNodes) >= SlowThreshold

(* Check if a slot is safe to skip *)
IsSafeToSkip(slot) ==
    LET skipVotes == GetVotes(slot, "SkipVote")
        fallbackVotes == GetVotes(slot, "SkipFallbackVote")
        allVotes == skipVotes \union fallbackVotes
        votingNodes == {v.node : v \in allVotes}
    IN TotalStake(votingNodes) >= SlowThreshold

(* =============================================================================
 * VOTE GENERATION
 * ============================================================================= *)

(* Generate a NotarVote *)
GenerateNotarVote(node, slot, hash) ==
    /\ node \in Nodes
    /\ slot \in Slots
    /\ hash \in STRING
    /\ votes' = votes \union {[node |-> node, slot |-> slot, type |-> "NotarVote", hash |-> hash, timestamp |-> 0]}
    /\ UNCHANGED <<certificates, fastFinalized, slowFinalized, notarized, skipped, timeouts, safeToNotar, safeToSkip>>

(* Generate a NotarFallbackVote *)
GenerateNotarFallbackVote(node, slot, hash) ==
    /\ node \in Nodes
    /\ slot \in Slots
    /\ hash \in STRING
    /\ slot \in safeToNotar
    /\ votes' = votes \union {[node |-> node, slot |-> slot, type |-> "NotarFallbackVote", hash |-> hash, timestamp |-> 0]}
    /\ UNCHANGED <<certificates, fastFinalized, slowFinalized, notarized, skipped, timeouts, safeToNotar, safeToSkip>>

(* Generate a SkipVote *)
GenerateSkipVote(node, slot) ==
    /\ node \in Nodes
    /\ slot \in Slots
    /\ votes' = votes \union {[node |-> node, slot |-> slot, type |-> "SkipVote", hash |-> "skip", timestamp |-> 0]}
    /\ UNCHANGED <<certificates, fastFinalized, slowFinalized, notarized, skipped, timeouts, safeToNotar, safeToSkip>>

(* Generate a SkipFallbackVote *)
GenerateSkipFallbackVote(node, slot) ==
    /\ node \in Nodes
    /\ slot \in Slots
    /\ slot \in safeToSkip
    /\ votes' = votes \union {[node |-> node, slot |-> slot, type |-> "SkipFallbackVote", hash |-> "skip", timestamp |-> 0]}
    /\ UNCHANGED <<certificates, fastFinalized, slowFinalized, notarized, skipped, timeouts, safeToNotar, safeToSkip>>

(* Generate a FinalVote *)
GenerateFinalVote(node, slot, hash) ==
    /\ node \in Nodes
    /\ slot \in Slots
    /\ hash \in STRING
    /\ [slot |-> slot, hash |-> hash] \in notarized
    /\ votes' = votes \union {[node |-> node, slot |-> slot, type |-> "FinalVote", hash |-> hash, timestamp |-> 0]}
    /\ UNCHANGED <<certificates, fastFinalized, slowFinalized, notarized, skipped, timeouts, safeToNotar, safeToSkip>>

(* =============================================================================
 * CERTIFICATE AGGREGATION
 * ============================================================================= *)

(* Aggregate NotarVotes into FastFinalization certificate *)
AggregateFastFinalization(slot, hash) ==
    LET notarVotes == GetVotes(slot, "NotarVote")
        votingNodes == {v.node : v \in notarVotes}
        totalStake == TotalStake(votingNodes)
    IN /\ totalStake >= FastThreshold
       /\ certificates' = certificates \union {[type |-> "FastFinalization", slot |-> slot, hash |-> hash, stake |-> totalStake, timestamp |-> 0]}
       /\ fastFinalized' = fastFinalized \union {[slot |-> slot, hash |-> hash]}
       /\ UNCHANGED <<votes, slowFinalized, notarized, skipped, timeouts, safeToNotar, safeToSkip>>

(* Aggregate NotarVotes into Notarization certificate *)
AggregateNotarization(slot, hash) ==
    LET notarVotes == GetVotes(slot, "NotarVote")
        votingNodes == {v.node : v \in notarVotes}
        totalStake == TotalStake(votingNodes)
    IN /\ totalStake >= SlowThreshold
       /\ certificates' = certificates \union {[type |-> "Notarization", slot |-> slot, hash |-> hash, stake |-> totalStake, timestamp |-> 0]}
       /\ notarized' = notarized \union {[slot |-> slot, hash |-> hash]}
       /\ UNCHANGED <<votes, fastFinalized, slowFinalized, skipped, timeouts, safeToNotar, safeToSkip>>

(* Aggregate NotarFallbackVotes into NotarFallback certificate *)
AggregateNotarFallback(slot, hash) ==
    LET notarVotes == GetVotes(slot, "NotarVote")
        fallbackVotes == GetVotes(slot, "NotarFallbackVote")
        allVotes == notarVotes \union fallbackVotes
        votingNodes == {v.node : v \in allVotes}
        totalStake == TotalStake(votingNodes)
    IN /\ totalStake >= SlowThreshold
       /\ certificates' = certificates \union {[type |-> "NotarFallback", slot |-> slot, hash |-> hash, stake |-> totalStake, timestamp |-> 0]}
       /\ notarized' = notarized \union {[slot |-> slot, hash |-> hash]}
       /\ UNCHANGED <<votes, fastFinalized, slowFinalized, skipped, timeouts, safeToNotar, safeToSkip>>

(* Aggregate SkipVotes into Skip certificate *)
AggregateSkip(slot) ==
    LET skipVotes == GetVotes(slot, "SkipVote")
        fallbackVotes == GetVotes(slot, "SkipFallbackVote")
        allVotes == skipVotes \union fallbackVotes
        votingNodes == {v.node : v \in allVotes}
        totalStake == TotalStake(votingNodes)
    IN /\ totalStake >= SlowThreshold
       /\ certificates' = certificates \union {[type |-> "Skip", slot |-> slot, hash |-> "skip", stake |-> totalStake, timestamp |-> 0]}
       /\ skipped' = skipped \union {slot}
       /\ UNCHANGED <<votes, fastFinalized, slowFinalized, notarized, timeouts, safeToNotar, safeToSkip>>

(* Aggregate FinalVotes into Finalization certificate *)
AggregateFinalization(slot, hash) ==
    LET finalVotes == GetVotes(slot, "FinalVote")
        votingNodes == {v.node : v \in finalVotes}
        totalStake == TotalStake(votingNodes)
    IN /\ totalStake >= SlowThreshold
       /\ certificates' = certificates \union {[type |-> "Finalization", slot |-> slot, hash |-> hash, stake |-> totalStake, timestamp |-> 0]}
       /\ slowFinalized' = slowFinalized \union {[slot |-> slot, hash |-> hash]}
       /\ UNCHANGED <<votes, fastFinalized, notarized, skipped, timeouts, safeToNotar, safeToSkip>>

(* =============================================================================
 * TIMEOUT HANDLING
 * ============================================================================= *)

(* Trigger SafeToNotar event *)
TriggerSafeToNotar(slot) ==
    /\ slot \in Slots
    /\ IsSafeToNotar(slot)
    /\ slot \notin safeToNotar
    /\ safeToNotar' = safeToNotar \union {slot}
    /\ UNCHANGED <<votes, certificates, fastFinalized, slowFinalized, notarized, skipped, timeouts, safeToSkip>>

(* Trigger SafeToSkip event *)
TriggerSafeToSkip(slot) ==
    /\ slot \in Slots
    /\ IsSafeToSkip(slot)
    /\ slot \notin safeToSkip
    /\ safeToSkip' = safeToSkip \union {slot}
    /\ UNCHANGED <<votes, certificates, fastFinalized, slowFinalized, notarized, skipped, timeouts, safeToNotar>>

(* Update timeout for a slot *)
UpdateTimeout(slot, newTimeout) ==
    /\ slot \in Slots
    /\ timeouts' = [s \in Slots |-> IF s = slot THEN newTimeout ELSE timeouts[s]]
    /\ UNCHANGED <<votes, certificates, fastFinalized, slowFinalized, notarized, skipped, safeToNotar, safeToSkip>>

(* =============================================================================
 * DUAL-PATH LOGIC
 * ============================================================================= *)

(* Fast path finalization *)
FastPathFinalization(slot, hash) ==
    LET notarVotes == GetVotes(slot, "NotarVote")
        votingNodes == {v.node : v \in notarVotes}
        totalStake == TotalStake(votingNodes)
    IN /\ totalStake >= FastThreshold
       /\ certificates' = certificates \union {[type |-> "FastFinalization", slot |-> slot, hash |-> hash, stake |-> totalStake, timestamp |-> 0]}
       /\ fastFinalized' = fastFinalized \union {[slot |-> slot, hash |-> hash]}
       /\ UNCHANGED <<votes, slowFinalized, notarized, skipped, timeouts, safeToNotar, safeToSkip>>

(* Slow path finalization *)
SlowPathFinalization(slot, hash) ==
    LET notarVotes == GetVotes(slot, "NotarVote")
        fallbackVotes == GetVotes(slot, "NotarFallbackVote")
        allVotes == notarVotes \union fallbackVotes
        votingNodes == {v.node : v \in allVotes}
        totalStake == TotalStake(votingNodes)
    IN /\ totalStake >= SlowThreshold
       /\ certificates' = certificates \union {[type |-> "NotarFallback", slot |-> slot, hash |-> hash, stake |-> totalStake, timestamp |-> 0]}
       /\ slowFinalized' = slowFinalized \union {[slot |-> slot, hash |-> hash]}
       /\ UNCHANGED <<votes, fastFinalized, notarized, skipped, timeouts, safeToNotar, safeToSkip>>

(* =============================================================================
 * INITIAL STATE
 * ============================================================================= *)

Init ==
    /\ votes = {}
    /\ certificates = {}
    /\ fastFinalized = {}
    /\ slowFinalized = {}
    /\ notarized = {}
    /\ skipped = {}
    /\ timeouts = [s \in Slots |-> 0]
    /\ safeToNotar = {}
    /\ safeToSkip = {}

(* =============================================================================
 * NEXT STATE RELATION
 * ============================================================================= *)

Next ==
    \/ \E node \in Nodes, slot \in Slots, hash \in STRING :
        GenerateNotarVote(node, slot, hash)
    \/ \E node \in Nodes, slot \in Slots, hash \in STRING :
        GenerateNotarFallbackVote(node, slot, hash)
    \/ \E node \in Nodes, slot \in Slots :
        GenerateSkipVote(node, slot)
    \/ \E node \in Nodes, slot \in Slots :
        GenerateSkipFallbackVote(node, slot)
    \/ \E node \in Nodes, slot \in Slots, hash \in STRING :
        GenerateFinalVote(node, slot, hash)
    \/ \E slot \in Slots, hash \in STRING :
        AggregateFastFinalization(slot, hash)
    \/ \E slot \in Slots, hash \in STRING :
        AggregateNotarization(slot, hash)
    \/ \E slot \in Slots, hash \in STRING :
        AggregateNotarFallback(slot, hash)
    \/ \E slot \in Slots :
        AggregateSkip(slot)
    \/ \E slot \in Slots, hash \in STRING :
        AggregateFinalization(slot, hash)
    \/ \E slot \in Slots :
        TriggerSafeToNotar(slot)
    \/ \E slot \in Slots :
        TriggerSafeToSkip(slot)
    \/ \E slot \in Slots, newTimeout \in Nat :
        UpdateTimeout(slot, newTimeout)
    \/ \E slot \in Slots, hash \in STRING :
        FastPathFinalization(slot, hash)
    \/ \E slot \in Slots, hash \in STRING :
        SlowPathFinalization(slot, hash)

(* =============================================================================
 * SPECIFICATION
 * ============================================================================= *)

Spec == Init /\ [][Next]_vars

(* =============================================================================
 * SAFETY PROPERTIES
 * ============================================================================= *)

(* No conflicting fast finalizations *)
FastSafety ==
    \A s \in Slots : 
        \A b1, b2 \in fastFinalized : 
            (b1.slot = s /\ b2.slot = s) => b1 = b2

(* No conflicting slow finalizations *)
SlowSafety ==
    \A s \in Slots : 
        \A b1, b2 \in slowFinalized : 
            (b1.slot = s /\ b2.slot = s) => b1 = b2

(* Certificate uniqueness *)
CertificateUniqueness ==
    \A cert1, cert2 \in certificates :
        (cert1.type = cert2.type /\ cert1.slot = cert2.slot) => cert1 = cert2

(* =============================================================================
 * LIVENESS PROPERTIES
 * ============================================================================= *)

(* Fast path completion *)
FastPathCompletion ==
    (TotalStake(Nodes) >= FastThreshold) => 
        \E b \in fastFinalized : TRUE

(* Slow path completion *)
SlowPathCompletion ==
    (TotalStake(Nodes) >= SlowThreshold) => 
        \E b \in slowFinalized : TRUE

(* =============================================================================
 * INVARIANTS
 * ============================================================================= *)

Invariants ==
    /\ TypeOK
    /\ FastSafety
    /\ SlowSafety
    /\ CertificateUniqueness

(* =============================================================================
 * THEOREMS
 * ============================================================================= *)

THEOREM Spec => []Invariants

(* =============================================================================
 * END OF MODULE
 * ============================================================================= *)

====

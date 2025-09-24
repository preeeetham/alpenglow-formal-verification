---- MODULE LargeScaleConfig ----
EXTENDS Naturals, FiniteSets

(*
 * Large-Scale Alpenglow Configuration for Statistical Model Checking
 * Designed for 10-100+ nodes with Monte Carlo sampling
 *)

CONSTANTS
    NodeCount,        \* Number of nodes (10-100)
    SlotCount,        \* Number of slots to process
    HashVariants,     \* Number of different block hashes
    ByzantineCount,   \* Number of Byzantine nodes
    CrashedCount,     \* Number of crashed nodes
    NetworkDelay,     \* Maximum network delay
    StakeDistribution \* Stake distribution function

VARIABLES
    votes,           \* Vote pool: <<node, slot, type, hash>>
    finalized,       \* Finalized blocks: <<slot, hash>>
    fastFinalized,   \* Fast-finalized blocks: <<slot, hash>>
    certificates,    \* Certificates: <<type, slot, hash, stake>>
    network,         \* Network state
    byzantineNodes,  \* Set of Byzantine nodes
    crashedNodes,    \* Set of crashed nodes
    currentSlot      \* Current slot being processed

vars == <<votes, finalized, fastFinalized, certificates, network, byzantineNodes, crashedNodes, currentSlot>>

(* =============================================================================
 * LARGE-SCALE PARAMETERS
 * ============================================================================= *)

Nodes == 1..NodeCount
Slots == 1..SlotCount
Hashes == {"A", "B", "C", "D", "E", "F", "G", "H"}[1..HashVariants]
VoteTypes == {"NotarVote", "FinalVote"}

(* Stake distribution - can be equal or weighted *)
EqualStake == [n \in Nodes |-> 100 / NodeCount]
WeightedStake == StakeDistribution  \* Custom distribution

Stake == IF StakeDistribution = "equal" THEN EqualStake ELSE WeightedStake

(* =============================================================================
 * BYZANTINE AND CRASH MODELING
 * ============================================================================= *)

(* Byzantine nodes behave adversarially *)
ByzantineBehavior(node, slot, hash) ==
    /\ node \in byzantineNodes
    /\ \E otherHash \in Hashes : otherHash # hash
    /\ votes' = votes \union {<<node, slot, "NotarVote", otherHash>>}
    /\ UNCHANGED <<finalized, fastFinalized, certificates, network, crashedNodes, currentSlot>>

(* Crashed nodes stop participating *)
CrashedBehavior(node) ==
    /\ node \in crashedNodes
    /\ UNCHANGED vars

(* =============================================================================
 * NETWORK DELAY MODELING
 * ============================================================================= *)

(* Message delivery with delay *)
DeliverMessage(from, to, message, delay) ==
    /\ from \in Nodes
    /\ to \in Nodes
    /\ delay \in 1..NetworkDelay
    /\ network' = [n \in Nodes |-> 
        IF n = to 
        THEN network[n] \union {<<from, message, delay>>}
        ELSE network[n]]
    /\ UNCHANGED <<votes, finalized, fastFinalized, certificates, byzantineNodes, crashedNodes, currentSlot>>

(* =============================================================================
 * STAKE CALCULATIONS FOR LARGE SCALE
 * ============================================================================= *)

(* Calculate stake for a set of nodes *)
TotalStake(nodes) ==
    Sum([n \in nodes |-> Stake[n]])

(* Get honest nodes (non-Byzantine, non-crashed) *)
HonestNodes == Nodes \ (byzantineNodes \union crashedNodes)

(* Calculate stake voting for a proposal *)
NotarStakeFor(slot, hash) ==
    LET votingNodes == {n \in Nodes : <<n, slot, "NotarVote", hash>> \in votes}
    IN TotalStake(votingNodes)

FinalStakeFor(slot, hash) ==
    LET votingNodes == {n \in Nodes : <<n, slot, "FinalVote", hash>> \in votes}
    IN TotalStake(votingNodes)

(* =============================================================================
 * LARGE-SCALE ACTIONS
 * ============================================================================= *)

(* Honest node votes *)
CastNotarVote(node, slot, hash) ==
    /\ node \in HonestNodes
    /\ <<node, slot, "NotarVote", hash>> \notin votes
    /\ votes' = votes \union {<<node, slot, "NotarVote", hash>>}
    /\ UNCHANGED <<finalized, fastFinalized, certificates, network, byzantineNodes, crashedNodes, currentSlot>>

CastFinalVote(node, slot, hash) ==
    /\ node \in HonestNodes
    /\ <<node, slot, "FinalVote", hash>> \notin votes
    /\ votes' = votes \union {<<node, slot, "FinalVote", hash>>}
    /\ UNCHANGED <<finalized, fastFinalized, certificates, network, byzantineNodes, crashedNodes, currentSlot>>

(* Fast finalization with 80% threshold *)
FastFinalize(slot, hash) ==
    /\ NotarStakeFor(slot, hash) >= 80
    /\ <<slot, hash>> \notin fastFinalized
    /\ fastFinalized' = fastFinalized \union {<<slot, hash>>}
    /\ finalized' = finalized \union {<<slot, hash>>}
    /\ certificates' = certificates \union {<<"FastFinalization", slot, hash, NotarStakeFor(slot, hash)>>}
    /\ UNCHANGED <<votes, network, byzantineNodes, crashedNodes, currentSlot>>

(* Slow finalization with 60% threshold *)
SlowFinalize(slot, hash) ==
    /\ FinalStakeFor(slot, hash) >= 60
    /\ <<slot, hash>> \notin finalized
    /\ finalized' = finalized \union {<<slot, hash>>}
    /\ certificates' = certificates \union {<<"Finalization", slot, hash, FinalStakeFor(slot, hash)>>}
    /\ UNCHANGED <<votes, fastFinalized, network, byzantineNodes, crashedNodes, currentSlot>>

(* =============================================================================
 * INITIAL STATE
 * ============================================================================= *)

Init ==
    /\ votes = {}
    /\ finalized = {}
    /\ fastFinalized = {}
    /\ certificates = {}
    /\ network = [n \in Nodes |-> {}]
    /\ byzantineNodes = {}  \* Will be set by configuration
    /\ crashedNodes = {}    \* Will be set by configuration
    /\ currentSlot = 1

(* =============================================================================
 * NEXT STATE RELATION
 * ============================================================================= *)

Next ==
    \/ \E node \in HonestNodes, slot \in Slots, hash \in Hashes :
        CastNotarVote(node, slot, hash)
    \/ \E node \in HonestNodes, slot \in Slots, hash \in Hashes :
        CastFinalVote(node, slot, hash)
    \/ \E node \in byzantineNodes, slot \in Slots, hash \in Hashes :
        ByzantineBehavior(node, slot, hash)
    \/ \E slot \in Slots, hash \in Hashes :
        FastFinalize(slot, hash)
    \/ \E slot \in Slots, hash \in Hashes :
        SlowFinalize(slot, hash)
    \/ \E from \in Nodes, to \in Nodes, message \in STRING, delay \in 1..NetworkDelay :
        DeliverMessage(from, to, message, delay)

Spec == Init /\ [][Next]_vars

(* =============================================================================
 * LARGE-SCALE SAFETY PROPERTIES
 * ============================================================================= *)

(* Core safety - no conflicting finalizations *)
Safety ==
    \A b1, b2 \in finalized :
        b1[1] = b2[1] => b1[2] = b2[2]

(* Fast path safety *)
FastSafety ==
    \A b1, b2 \in fastFinalized :
        b1[1] = b2[1] => b1[2] = b2[2]

(* Byzantine resilience *)
ByzantineSafety ==
    TotalStake(byzantineNodes) < 20 =>
        \A b1, b2 \in finalized :
            b1[1] = b2[1] => b1[2] = b2[2]

(* Crash resilience *)
CrashLiveness ==
    TotalStake(byzantineNodes) < 20 /\
    TotalStake(crashedNodes) < 20 =>
        TotalStake(HonestNodes) > 60

(* =============================================================================
 * STATISTICAL PROPERTIES
 * ============================================================================= *)

(* Probability of safety under random failures *)
ProbabilisticSafety ==
    \A failureRate \in 0..20 :
        Cardinality(byzantineNodes) <= (NodeCount * failureRate) / 100 =>
            []Safety

(* Expected finalization time *)
ExpectedFinalizationTime ==
    \A slot \in Slots :
        \E hash \in Hashes :
            <<slot, hash>> \in finalized =>
                FinalizationTime(slot, hash) <= 2 * NetworkDelay

(* =============================================================================
 * MONTE CARLO SAMPLING
 * ============================================================================= *)

(* Random Byzantine node selection *)
RandomByzantineSelection ==
    \E randomNodes \in SUBSET Nodes :
        Cardinality(randomNodes) = ByzantineCount /\
        byzantineNodes' = randomNodes

(* Random crash node selection *)
RandomCrashSelection ==
    \E randomNodes \in SUBSET Nodes :
        Cardinality(randomNodes) = CrashedCount /\
        crashedNodes' = randomNodes

(* =============================================================================
 * INVARIANTS FOR LARGE SCALE
 * ============================================================================= *)

LargeScaleInvariants ==
    /\ Safety
    /\ FastSafety
    /\ ByzantineSafety
    /\ Cardinality(byzantineNodes) <= ByzantineCount
    /\ Cardinality(crashedNodes) <= CrashedCount
    /\ TotalStake(byzantineNodes) <= 20
    /\ TotalStake(crashedNodes) <= 20

(* =============================================================================
 * SPECIFICATION
 * ============================================================================= *)

Init ==
    /\ votes = {}
    /\ finalized = {}
    /\ byzantineNodes = {}
    /\ crashedNodes = {}

Next ==
    \/ VoteAction
    /\ RandomByzantineSelection
    /\ RandomCrashSelection
    /\ FastFinalize
    /\ SlowFinalize

Spec == Init /\ [][Next]_vars

THEOREM Spec => []LargeScaleInvariants

====

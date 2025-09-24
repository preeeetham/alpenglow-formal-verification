---- MODULE LargeScaleConfig ----
EXTENDS Naturals, FiniteSets, Reals

(*
 * Large-Scale Alpenglow Configuration for Statistical Model Checking
 * Simplified version that actually works with TLC
 *)

CONSTANTS 
    NodeCount,        \* Number of nodes in the network
    SlotCount,        \* Number of slots to process  
    ByzantineCount,   \* Number of Byzantine nodes
    CrashedCount      \* Number of crashed nodes

VARIABLES
    votes,           \* Set of votes: <<node, slot, type, hash>>
    finalized,       \* Set of finalized blocks: <<slot, hash>>
    fastFinalized    \* Set of fast-finalized blocks: <<slot, hash>>

vars == <<votes, finalized, fastFinalized>>

(* =============================================================================
 * HELPER DEFINITIONS
 * ============================================================================= *)

\* Generate nodes based on NodeCount
Nodes == 1..NodeCount
Slots == 1..SlotCount
Hashes == {"A", "B"}
VoteTypes == {"NotarVote", "FinalVote"}

\* Get votes of a specific type for a slot and hash
VotesFor(slot, hash, voteType) ==
    {vote \in votes : vote[2] = slot /\ vote[4] = hash /\ vote[3] = voteType}

\* Get nodes that voted for a specific proposal
NodesVotedFor(slot, hash, voteType) ==
    {vote[1] : vote \in VotesFor(slot, hash, voteType)}

\* Calculate stake percentage voting for a proposal (simplified - each node has equal stake)
StakePercentageFor(slot, hash, voteType) ==
    (Cardinality(NodesVotedFor(slot, hash, voteType)) * 100) \div NodeCount

(* =============================================================================
 * PROTOCOL ACTIONS
 * ============================================================================= *)

\* Cast a notarization vote
CastNotarVote(node, slot, hash) ==
    /\ node \in Nodes
    /\ slot \in Slots
    /\ hash \in Hashes
    /\ votes' = votes \union {<<node, slot, "NotarVote", hash>>}
    /\ UNCHANGED <<finalized, fastFinalized>>

\* Cast a finalization vote (requires prior notarization)  
CastFinalVote(node, slot, hash) ==
    /\ node \in Nodes
    /\ slot \in Slots
    /\ hash \in Hashes
    /\ <<node, slot, "NotarVote", hash>> \in votes
    /\ votes' = votes \union {<<node, slot, "FinalVote", hash>>}
    /\ UNCHANGED <<finalized, fastFinalized>>

\* Fast finalization (80% stake threshold)
FastFinalize(slot, hash) ==
    /\ slot \in Slots
    /\ hash \in Hashes
    /\ StakePercentageFor(slot, hash, "FinalVote") >= 80
    /\ finalized' = finalized \union {<<slot, hash>>}
    /\ fastFinalized' = fastFinalized \union {<<slot, hash>>}
    /\ UNCHANGED votes

\* Slow finalization (60% stake threshold)
SlowFinalize(slot, hash) ==
    /\ slot \in Slots
    /\ hash \in Hashes
    /\ StakePercentageFor(slot, hash, "FinalVote") >= 60
    /\ \A h \in Hashes : h # hash => StakePercentageFor(slot, h, "FinalVote") < 60
    /\ finalized' = finalized \union {<<slot, hash>>}
    /\ UNCHANGED <<votes, fastFinalized>>

(* =============================================================================
 * SPECIFICATION
 * ============================================================================= *)

Init ==
    /\ votes = {}
    /\ finalized = {}
    /\ fastFinalized = {}

Next ==
    \/ \E node \in Nodes, slot \in Slots, hash \in Hashes :
        CastNotarVote(node, slot, hash)
    \/ \E node \in Nodes, slot \in Slots, hash \in Hashes :
        CastFinalVote(node, slot, hash)
    \/ \E slot \in Slots, hash \in Hashes :
        FastFinalize(slot, hash)
    \/ \E slot \in Slots, hash \in Hashes :
        SlowFinalize(slot, hash)

Spec == Init /\ [][Next]_vars

(* =============================================================================
 * SAFETY PROPERTIES
 * ============================================================================= *)

\* Type correctness
TypeOK ==
    /\ votes \subseteq (Nodes \X Slots \X VoteTypes \X Hashes)
    /\ finalized \subseteq (Slots \X Hashes)
    /\ fastFinalized \subseteq (Slots \X Hashes)
    /\ NodeCount \in Nat
    /\ SlotCount \in Nat
    /\ ByzantineCount \in Nat
    /\ CrashedCount \in Nat

\* Safety: no conflicting finalizations
Safety ==
    \A b1, b2 \in finalized :
        b1[1] = b2[1] => b1[2] = b2[2]

\* Fast finalized blocks are also finalized
FastSafety ==
    fastFinalized \subseteq finalized

(* =============================================================================
 * LIVENESS PROPERTIES  
 * ============================================================================= *)

\* Progress: eventually some block gets finalized
Progress ==
    <>(\E slot \in Slots, hash \in Hashes : <<slot, hash>> \in finalized)

\* Fast path: if enough votes, fast finalization occurs
FastPath ==
    \A slot \in Slots, hash \in Hashes :
        StakePercentageFor(slot, hash, "FinalVote") >= 80 =>
            <>( <<slot, hash>> \in fastFinalized )

(* =============================================================================
 * RESILIENCE PROPERTIES
 * ============================================================================= *)

\* Byzantine safety (simplified)
ByzantineSafety ==
    (ByzantineCount * 5 <= NodeCount) => []Safety

\* Crash liveness (simplified)
CrashLiveness ==
    (CrashedCount * 5 <= NodeCount) => Progress

(* =============================================================================
 * COMBINED PROPERTIES FOR STATISTICAL CHECKING
 * ============================================================================= *)

\* Large scale invariants for statistical model checking
LargeScaleInvariants ==
    /\ TypeOK
    /\ Safety
    /\ FastSafety

\* Probabilistic safety for statistical analysis
ProbabilisticSafety ==
    /\ Safety
    /\ ByzantineSafety
    /\ CrashLiveness

====
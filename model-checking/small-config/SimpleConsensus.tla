---- MODULE SimpleConsensus ----
EXTENDS Naturals, FiniteSets

(*
 * Simplified Alpenglow Consensus for Model Checking
 *)

CONSTANTS
    Nodes,           \* Set of validator nodes
    Slots            \* Set of time slots

VARIABLES
    votes,           \* Vote pool
    finalized,       \* Finalized blocks
    fastFinalized    \* Fast-path finalized blocks

vars == <<votes, finalized, fastFinalized>>

(* Stake distribution - equal 25% each (as integers) *)
Stake == [n \in Nodes |-> 25]

(* Calculate total stake for a set of nodes *)
TotalStake(nodeSet) == Cardinality(nodeSet) * 25

(* Type definitions *)
Vote == [node: Nodes, slot: Slots, type: {"NotarVote", "FinalVote"}, hash: {"A", "B"}]

TypeOK ==
    /\ votes \subseteq Vote
    /\ finalized \subseteq [slot: Slots, hash: {"A", "B"}]
    /\ fastFinalized \subseteq [slot: Slots, hash: {"A", "B"}]

(* Initial state *)
Init ==
    /\ votes = {}
    /\ finalized = {}
    /\ fastFinalized = {}

(* Generate a vote *)
CastVote(node, slot, voteType, hash) ==
    /\ votes' = votes \union {[node |-> node, slot |-> slot, type |-> voteType, hash |-> hash]}
    /\ UNCHANGED <<finalized, fastFinalized>>

(* Fast path finalization (80% threshold) *)
FastFinalize(slot, hash) ==
    LET notarVotes == {v \in votes : v.slot = slot /\ v.type = "NotarVote" /\ v.hash = hash}
        votingNodes == {v.node : v \in notarVotes}
        totalStake == TotalStake(votingNodes)
    IN /\ totalStake >= 80
       /\ fastFinalized' = fastFinalized \union {[slot |-> slot, hash |-> hash]}
       /\ finalized' = finalized \union {[slot |-> slot, hash |-> hash]}
       /\ UNCHANGED votes

(* Slow path finalization (60% threshold) *)
SlowFinalize(slot, hash) ==
    LET notarVotes == {v \in votes : v.slot = slot /\ v.type = "NotarVote" /\ v.hash = hash}
        finalVotes == {v \in votes : v.slot = slot /\ v.type = "FinalVote" /\ v.hash = hash}
        allVotes == notarVotes \union finalVotes
        votingNodes == {v.node : v \in allVotes}
        totalStake == TotalStake(votingNodes)
    IN /\ totalStake >= 60
       /\ finalized' = finalized \union {[slot |-> slot, hash |-> hash]}
       /\ UNCHANGED <<votes, fastFinalized>>

(* Next state transitions *)
Next ==
    \/ \E node \in Nodes, slot \in Slots, voteType \in {"NotarVote", "FinalVote"}, hash \in {"A", "B"} :
        CastVote(node, slot, voteType, hash)
    \/ \E slot \in Slots, hash \in {"A", "B"} :
        FastFinalize(slot, hash)
    \/ \E slot \in Slots, hash \in {"A", "B"} :
        SlowFinalize(slot, hash)

(* Specification *)
Spec == Init /\ [][Next]_vars

(* Safety Properties *)

(* No conflicting finalizations *)
Safety ==
    \A b1, b2 \in finalized :
        b1.slot = b2.slot => b1.hash = b2.hash

(* Fast finalized blocks are also finalized *)
FastImpliesFinalized ==
    fastFinalized \subseteq finalized

(* Dual-path consistency *)
DualPathConsistency ==
    \A slot \in Slots, hash \in {"A", "B"} :
        [slot |-> slot, hash |-> hash] \in fastFinalized =>
        \A otherHash \in {"A", "B"} : 
            otherHash # hash => [slot |-> slot, hash |-> otherHash] \notin finalized

(* All invariants *)
Invariants ==
    /\ TypeOK
    /\ Safety
    /\ FastImpliesFinalized
    /\ DualPathConsistency

THEOREM Spec => []Invariants

====

---- MODULE TinyConsensus ----
EXTENDS Naturals, FiniteSets

(*
 * Tiny Alpenglow Consensus for Quick Verification
 *)

CONSTANTS
    Nodes,           \* Set of validator nodes  
    Slots            \* Set of time slots

VARIABLES
    votes,           \* Vote pool
    finalized        \* Finalized blocks

vars == <<votes, finalized>>

(* Stake distribution - equal 25% each (as integers) *)
Stake == [n \in Nodes |-> 25]

(* Calculate total stake for a set of nodes *)
TotalStake(nodeSet) == Cardinality(nodeSet) * 25

(* Type definitions *)
Vote == [node: Nodes, slot: Slots, type: {"NotarVote"}, hash: {"A", "B"}]

TypeOK ==
    /\ votes \subseteq Vote
    /\ finalized \subseteq [slot: Slots, hash: {"A", "B"}]

(* Initial state *)
Init ==
    /\ votes = {}
    /\ finalized = {}

(* Generate a vote *)
CastVote(node, slot, hash) ==
    /\ votes' = votes \union {[node |-> node, slot |-> slot, type |-> "NotarVote", hash |-> hash]}
    /\ UNCHANGED finalized

(* Finalize when enough votes (80% threshold) *)
Finalize(slot, hash) ==
    LET notarVotes == {v \in votes : v.slot = slot /\ v.type = "NotarVote" /\ v.hash = hash}
        votingNodes == {v.node : v \in notarVotes}
        totalStake == TotalStake(votingNodes)
    IN /\ totalStake >= 80
       /\ finalized' = finalized \union {[slot |-> slot, hash |-> hash]}
       /\ UNCHANGED votes

(* Next state transitions *)
Next ==
    \/ \E node \in Nodes, slot \in Slots, hash \in {"A", "B"} :
        CastVote(node, slot, hash)
    \/ \E slot \in Slots, hash \in {"A", "B"} :
        Finalize(slot, hash)

(* Specification *)
Spec == Init /\ [][Next]_vars

(* Safety: No conflicting finalizations *)
Safety ==
    \A b1, b2 \in finalized :
        b1.slot = b2.slot => b1.hash = b2.hash

(* All invariants *)
Invariants ==
    /\ TypeOK
    /\ Safety

THEOREM Spec => []Invariants

====

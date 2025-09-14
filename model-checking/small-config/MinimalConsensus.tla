---- MODULE MinimalConsensus ----
EXTENDS Naturals, FiniteSets

(*
 * Minimal Alpenglow Consensus for Quick Testing
 * Only 2 nodes, 2 slots, 1 hash - very small state space
 *)

CONSTANTS N1, N2

VARIABLES 
    votes,          \* Set of votes: <<node, slot, type, hash>>
    finalized,      \* Set of finalized blocks: <<slot, hash>>
    fastFinalized   \* Set of fast-finalized blocks: <<slot, hash>>

vars == <<votes, finalized, fastFinalized>>

Nodes == {N1, N2}
Slots == {1, 2}
Hashes == {"A"}
VoteTypes == {"NotarVote", "FinalVote"}

(* Each node has 50% stake *)
StakePerNode == 50

TypeOK ==
    /\ votes \subseteq (Nodes \X Slots \X VoteTypes \X Hashes)
    /\ finalized \subseteq (Slots \X Hashes)
    /\ fastFinalized \subseteq (Slots \X Hashes)

(* Calculate stake voting for a specific proposal *)
NotarStakeFor(slot, hash) ==
    Cardinality({node \in Nodes : <<node, slot, "NotarVote", hash>> \in votes}) * StakePerNode

FinalStakeFor(slot, hash) ==
    Cardinality({node \in Nodes : <<node, slot, "FinalVote", hash>> \in votes}) * StakePerNode

(* Actions *)

(* A node can cast a NotarVote *)
CastNotarVote(node, slot, hash) ==
    /\ <<node, slot, "NotarVote", hash>> \notin votes
    /\ votes' = votes \union {<<node, slot, "NotarVote", hash>>}
    /\ UNCHANGED <<finalized, fastFinalized>>

(* A node can cast a FinalVote *)
CastFinalVote(node, slot, hash) ==
    /\ <<node, slot, "FinalVote", hash>> \notin votes
    /\ votes' = votes \union {<<node, slot, "FinalVote", hash>>}
    /\ UNCHANGED <<finalized, fastFinalized>>

(* Fast finalization with 80% stake (2 nodes = 100%, so 80% = 2 nodes) *)
FastFinalize(slot, hash) ==
    /\ NotarStakeFor(slot, hash) >= 80
    /\ <<slot, hash>> \notin fastFinalized
    /\ fastFinalized' = fastFinalized \union {<<slot, hash>>}
    /\ finalized' = finalized \union {<<slot, hash>>}
    /\ UNCHANGED votes

(* Slow finalization with 60% stake (2 nodes = 100%, so 60% = 2 nodes) *)
SlowFinalize(slot, hash) ==
    /\ FinalStakeFor(slot, hash) >= 60
    /\ <<slot, hash>> \notin finalized
    /\ finalized' = finalized \union {<<slot, hash>>}
    /\ UNCHANGED <<votes, fastFinalized>>

(* Next state relation *)
Next ==
    \/ \E node \in Nodes, slot \in Slots, hash \in Hashes :
        CastNotarVote(node, slot, hash)
    \/ \E node \in Nodes, slot \in Slots, hash \in Hashes :
        CastFinalVote(node, slot, hash)
    \/ \E slot \in Slots, hash \in Hashes :
        FastFinalize(slot, hash)
    \/ \E slot \in Slots, hash \in Hashes :
        SlowFinalize(slot, hash)

(* Initial state *)
Init ==
    /\ votes = {}
    /\ finalized = {}
    /\ fastFinalized = {}

(* Specification *)
Spec == Init /\ [][Next]_vars

(* Safety: No conflicting finalizations *)
Safety ==
    \A b1, b2 \in finalized :
        b1[1] = b2[1] => b1[2] = b2[2]

(* Type safety *)
TypeSafety == TypeOK

(* All invariants *)
SafetyInvariants ==
    /\ TypeSafety
    /\ Safety

THEOREM Spec => []SafetyInvariants

====

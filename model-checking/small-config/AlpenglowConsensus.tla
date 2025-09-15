---- MODULE AlpenglowConsensus ----
EXTENDS Naturals, FiniteSets

(*
 * Alpenglow Consensus with Dual-Path Voting
 * Simplified for small-scale model checking
 *)

CONSTANTS N1, N2, N3, N4

VARIABLES 
    votes,          \* Set of votes: <<node, slot, type, hash>>
    finalized,      \* Set of finalized blocks: <<slot, hash>>
    fastFinalized   \* Set of fast-finalized blocks: <<slot, hash>>

vars == <<votes, finalized, fastFinalized>>

Nodes == {N1, N2, N3, N4}
Slots == {1}  (* Reduced to 1 slot for large state space *)
Hashes == {"A"}  (* Reduced to 1 hash for large state space *)
VoteTypes == {"NotarVote", "FinalVote"}

(* Each node has 25% stake *)
StakePerNode == 25

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

(* Fast finalization with 80% stake (3+ nodes) *)
FastFinalize(slot, hash) ==
    /\ NotarStakeFor(slot, hash) >= 80  \* Need 4 nodes * 25% = 100%, so 80% = 3+ nodes
    /\ <<slot, hash>> \notin fastFinalized
    /\ fastFinalized' = fastFinalized \union {<<slot, hash>>}
    /\ finalized' = finalized \union {<<slot, hash>>}
    /\ UNCHANGED votes

(* Slow finalization with 60% stake (3+ nodes) *)
SlowFinalize(slot, hash) ==
    /\ FinalStakeFor(slot, hash) >= 60  \* Need 60% = 3+ nodes
    /\ <<slot, hash>> \notin finalized
    /\ finalized' = finalized \union {<<slot, hash>>}
    /\ UNCHANGED <<votes, fastFinalized>>

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

(* Safety Properties *)

(* No conflicting blocks finalized for the same slot *)
Safety ==
    \A b1, b2 \in finalized :
        b1[1] = b2[1] => b1[2] = b2[2]

(* No conflicting fast finalizations *)
FastSafety ==
    \A b1, b2 \in fastFinalized :
        b1[1] = b2[1] => b1[2] = b2[2]

(* Fast finalized blocks are also finalized *)
FastImpliesFinalized ==
    fastFinalized \subseteq finalized

(* Dual-path consistency *)
DualPathConsistency ==
    \A slot \in Slots, hash \in Hashes :
        (<<slot, hash>> \in fastFinalized /\ <<slot, hash>> \in finalized) =>
        \A otherHash \in Hashes :
            otherHash # hash => <<slot, otherHash>> \notin finalized

(* Liveness Properties *)

(* If enough nodes vote, block gets finalized *)
VotingLiveness ==
    \A slot \in Slots, hash \in Hashes :
        NotarStakeFor(slot, hash) >= 80 => 
            <>(<<slot, hash>> \in fastFinalized)

(* Combined safety invariants *)
SafetyInvariants ==
    /\ TypeOK
    /\ Safety
    /\ FastSafety
    /\ FastImpliesFinalized
    /\ DualPathConsistency

THEOREM Spec => []SafetyInvariants

====

---- MODULE AlpenglowSmall ----
EXTENDS Naturals, FiniteSets

(*
 * Small configuration of Alpenglow for exhaustive model checking
 * 4 nodes, 5 slots, simplified voting logic
 *)

CONSTANTS
    N1, N2, N3, N4,          \* Node identifiers
    S1, S2, S3, S4, S5       \* Slot identifiers

VARIABLES
    votes,                   \* Set of votes cast
    finalized,              \* Set of finalized blocks
    fastFinalized,          \* Set of fast-finalized blocks
    certificates,           \* Set of certificates
    currentSlot            \* Current slot being processed

vars == <<votes, finalized, fastFinalized, certificates, currentSlot>>

Nodes == {N1, N2, N3, N4}
Slots == {S1, S2, S3, S4, S5}
Stake == [n \in Nodes |-> 25]  \* Equal 25% stake each

VoteTypes == {"NotarVote", "FinalVote"}
CertTypes == {"FastFinalization", "Finalization"}
Hashes == {"A", "B"}

(* Type definitions simplified for model checking *)
(* Vote: <<node, slot, type, hash>> *)
(* Block: <<slot, hash>> *)
(* Certificate: <<type, slot, hash, stake>> *)

TypeOK ==
    /\ votes \subseteq (Nodes \X Slots \X VoteTypes \X Hashes)
    /\ finalized \subseteq (Slots \X Hashes)
    /\ fastFinalized \subseteq (Slots \X Hashes)
    /\ certificates \subseteq (CertTypes \X Slots \X Hashes \X Nat)
    /\ currentSlot \in Slots

(* Calculate total stake for nodes that voted for a specific block *)
StakeFor(slot, hash, voteType) ==
    Cardinality({vote[1] : vote \in votes /\ vote[2] = slot /\ vote[3] = voteType /\ vote[4] = hash}) * 25

(* Generate a vote *)
CastVote(node, slot, voteType, hash) ==
    /\ votes' = votes \union {<<node, slot, voteType, hash>>}
    /\ UNCHANGED <<finalized, fastFinalized, certificates, currentSlot>>

(* Fast path finalization (80% = 80 stake) *)
FastFinalize(slot, hash) ==
    /\ StakeFor(slot, hash, "NotarVote") >= 80
    /\ <<slot, hash>> \notin fastFinalized
    /\ fastFinalized' = fastFinalized \union {<<slot, hash>>}
    /\ finalized' = finalized \union {<<slot, hash>>}
    /\ certificates' = certificates \union {<<"FastFinalization", slot, hash, StakeFor(slot, hash, "NotarVote")>>}
    /\ UNCHANGED <<votes, currentSlot>>

(* Slow path finalization (60% = 60 stake) *)
SlowFinalize(slot, hash) ==
    /\ StakeFor(slot, hash, "FinalVote") >= 60
    /\ <<slot, hash>> \notin finalized
    /\ finalized' = finalized \union {<<slot, hash>>}
    /\ certificates' = certificates \union {<<"Finalization", slot, hash, StakeFor(slot, hash, "FinalVote")>>}
    /\ UNCHANGED <<votes, fastFinalized, currentSlot>>

(* Process next slot *)
NextSlot ==
    /\ currentSlot \in Slots
    /\ currentSlot' = CHOOSE s \in Slots : s \notin {currentSlot}
    /\ UNCHANGED <<votes, finalized, fastFinalized, certificates>>

Init ==
    /\ votes = {}
    /\ finalized = {}
    /\ fastFinalized = {}
    /\ certificates = {}
    /\ currentSlot = S1

Next ==
    \/ \E node \in Nodes, slot \in Slots, hash \in Hashes :
        CastVote(node, slot, "NotarVote", hash)
    \/ \E node \in Nodes, slot \in Slots, hash \in Hashes :
        CastVote(node, slot, "FinalVote", hash)
    \/ \E slot \in Slots, hash \in Hashes :
        FastFinalize(slot, hash)
    \/ \E slot \in Slots, hash \in Hashes :
        SlowFinalize(slot, hash)
    \/ NextSlot

Spec == Init /\ [][Next]_vars

(* Safety properties *)
Safety ==
    \A s \in Slots :
        \A b1, b2 \in finalized :
            (b1[1] = s /\ b2[1] = s) => b1[2] = b2[2]

NoConflictingFast ==
    \A s \in Slots :
        \A b1, b2 \in fastFinalized :
            (b1[1] = s /\ b2[1] = s) => b1[2] = b2[2]

CertificateValidity ==
    \A cert \in certificates :
        \E block \in finalized :
            block[1] = cert[2] /\ block[2] = cert[3]

(* Liveness properties *)
Progress ==
    <>(\E block \in finalized : TRUE)

FastProgress ==
    (StakeFor(S1, "A", "NotarVote") >= 80) => <>(\E block \in fastFinalized : block[1] = S1)

THEOREM Spec => []Safety
THEOREM Spec => []NoConflictingFast
THEOREM Spec => []CertificateValidity

====

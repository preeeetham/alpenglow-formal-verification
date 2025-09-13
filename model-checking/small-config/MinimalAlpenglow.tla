---- MODULE MinimalAlpenglow ----
EXTENDS Naturals, FiniteSets

(*
 * Minimal Alpenglow specification for testing basic safety properties
 *)

CONSTANTS N1, N2, N3, N4

VARIABLES finalized

Nodes == {N1, N2, N3, N4}

Init == finalized = {}

FinalizeBlock(node, slot, hash) ==
    finalized' = finalized \union {<<slot, hash>>}

Next ==
    \E node \in Nodes, slot \in {1, 2, 3}, hash \in {"A", "B"} :
        FinalizeBlock(node, slot, hash)

Spec == Init /\ [][Next]_finalized

(* Safety: No two different blocks finalized for same slot *)
Safety ==
    \A b1, b2 \in finalized :
        b1[1] = b2[1] => b1[2] = b2[2]

THEOREM Spec => []Safety

====

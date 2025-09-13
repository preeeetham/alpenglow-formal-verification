---- MODULE TestSpec ----
EXTENDS Naturals

VARIABLES x

Init == x = 0

Next == x' = x + 1

Spec == Init /\ [][Next]_x

====

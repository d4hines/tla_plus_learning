----------------------------- MODULE Networking -----------------------------
(*
EXTENDS Sequences

CONSTANT Nodes
CONSTANT Messages

VARIABLES message_queue

INIT == /\ message_queue = [node \in Nodes |-> <<>>]

-----------------------------------------------------------------------------

Spec == Init /\ [][Next]_vars
*)

EXTENDS Naturals
VARIABLE hr
HCini == hr \in (1 .. 12)
HCnxt == hr' = IF hr /= 12 THEN hr + 1 ELSE 1
HC == HCini /\ [][HCnxt]_hr
Init == HCini
Spec == HC => []HCini


=============================================================================
\* Modification History
\* Last modified Thu Dec 16 14:46:47 EST 2021 by d4hines
\* Created Thu Dec 16 11:31:53 EST 2021 by d4hines

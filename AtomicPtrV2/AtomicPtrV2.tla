------ MODULE AtomicPtrV2 ----
EXTENDS TLC, Naturals, Sequences

CONSTANTS Node

VARIABLES pointer, counter, objects, pc

vars == <<pointer, counter, objects, pc>>


Object == [ref: Nat, destroyed: Nat]


TypeOK ==
    /\ objects \in Seq(Object)
    /\ pointer \in DOMAIN objects
    /\ counter \in Nat
    /\ pc \in [Node -> {"Init", "Terminated"}]


Init ==
    /\ objects = <<[ref |-> 1, destroyed |-> 0]>>
    /\ pointer = 1
    /\ counter = 1
    /\ pc = [n \in Node |-> "Init"]


TerminateCond ==
    /\ TRUE

Terminated ==
    /\ TerminateCond
    /\ UNCHANGED vars


Next ==
    \/ Terminated

Spec == Init /\ [][Next]_vars

====
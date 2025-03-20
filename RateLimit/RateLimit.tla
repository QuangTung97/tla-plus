------ MODULE RateLimit ----
EXTENDS TLC, Naturals, FiniteSets

CONSTANTS Node, nil, max_running

VARIABLES pc, state

vars == <<pc, state>>

---------------------------------------------------------------------------------

State == [
    running: Nat
]

NullState == State \union {nil}

PC == {"Init", "HandleRequest", "Terminated"}

---------------------------------------------------------------------------------

TypeOK ==
    /\ pc \in [Node -> PC]
    /\ state \in NullState

Init ==
    /\ pc = [n \in Node |-> "Init"]
    /\ state = nil

---------------------------------------------------------------------------------

goto(n, l) ==
    pc' = [pc EXCEPT ![n] = l]


NodeWait(n) ==
    LET
        old_state ==
            IF state = nil
                THEN [running |-> 0]
                ELSE state

        when_normal ==
            /\ state' = [old_state EXCEPT !.running = @ + 1]
    IN
    /\ pc[n] = "Init"
    /\ goto(n, "HandleRequest")
    /\ IF old_state.running < max_running
        THEN when_normal
        ELSE TRUE

---------------------------------------------------------------------------------

TerminateCond ==
    /\ \A n \in Node: pc[n] = "Terminated"

Terminated ==
    /\ TerminateCond
    /\ UNCHANGED vars


Next ==
    \/ \E n \in Node:
        \/ NodeWait(n)
    \/ Terminated


Spec == Init /\ [][Next]_vars

---------------------------------------------------------------------------------

MaxNumRunningInv ==
    LET
        running_set == {n \in Node: pc[n] = "HandleRequest"}
    IN
        Cardinality(running_set) <= max_running

====

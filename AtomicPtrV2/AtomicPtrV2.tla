------ MODULE AtomicPtrV2 ----
EXTENDS TLC, Naturals, Sequences

CONSTANTS Node, nil

VARIABLES pointer, counter, objects, pc, local_addr

vars == <<pointer, counter, objects, pc, local_addr>>


Object == [ref: Nat, destroyed: Nat]


NullAddr == (DOMAIN objects) \union {nil}

State == {"Init", "StartSwapPtr", "DecreaseRef", "DestroyObject", "Terminated"}

TypeOK ==
    /\ objects \in Seq(Object)
    /\ pointer \in DOMAIN objects
    /\ counter \in Nat
    /\ pc \in [Node -> State]
    /\ local_addr \in [Node -> NullAddr]


Init ==
    /\ objects = <<[ref |-> 1, destroyed |-> 0]>>
    /\ pointer = 1
    /\ counter = 1
    /\ pc = [n \in Node |-> "Init"]
    /\ local_addr = [n \in Node |-> nil]



goto(n, l) ==
    /\ pc' = [pc EXCEPT ![n] = l]


AllocateNewObject(n) ==
    /\ pc[n] = "Init"
    /\ goto(n, "StartSwapPtr")
    /\ objects' = Append(objects, [ref |-> 1, destroyed |-> 0])
    /\ local_addr' = [local_addr EXCEPT ![n] = Len(objects')]
    /\ UNCHANGED <<counter, pointer>>


StartSwapPtr(n) ==
    /\ pc[n] = "StartSwapPtr"
    /\ goto(n, "DecreaseRef")
    /\ pointer' = local_addr[n]
    /\ local_addr' = [local_addr EXCEPT ![n] = pointer]
    /\ UNCHANGED counter
    /\ UNCHANGED objects


DecreaseRef(n) ==
    LET
        addr == local_addr[n]
    IN
        /\ pc[n] = "DecreaseRef"
        /\ goto(n, "DestroyObject")
        /\ objects' = [objects EXCEPT ![addr].ref = @ - 1]
        /\ UNCHANGED local_addr
        /\ UNCHANGED counter
        /\ UNCHANGED pointer


DestroyObject(n) ==
    LET
        addr == local_addr[n]
    IN
        /\ pc[n] = "DestroyObject"
        /\ goto(n, "Terminated")
        /\ objects' = [objects EXCEPT ![addr].destroyed = @ + 1]
        /\ UNCHANGED local_addr
        /\ UNCHANGED counter
        /\ UNCHANGED pointer


TerminateCond ==
    /\ \A n \in Node: pc[n] = "Terminated"

Terminated ==
    /\ TerminateCond
    /\ UNCHANGED vars


Next ==
    \/ \E n \in Node:
        \/ AllocateNewObject(n)
        \/ StartSwapPtr(n)
        \/ DecreaseRef(n)
        \/ DestroyObject(n)
    \/ Terminated

Spec == Init /\ [][Next]_vars


FullyDestroyed ==
    LET
        destroyedExceptLast(addr) ==
            addr # pointer => objects[addr].destroyed = 1

        allDestroyed ==
            \A addr \in DOMAIN objects: destroyedExceptLast(addr)
    IN
        TerminateCond => allDestroyed

====
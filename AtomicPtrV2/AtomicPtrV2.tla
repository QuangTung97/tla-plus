------ MODULE AtomicPtrV2 ----
EXTENDS TLC, Naturals, Sequences

CONSTANTS Node, nil

VARIABLES pointer, counter, objects, pc, local_addr, last_counter

vars == <<pointer, counter, objects, pc, local_addr, last_counter>>


Object == [ref: Nat, extra: Nat, added: BOOLEAN, destroyed: Nat]


NullAddr == (DOMAIN objects) \union {nil}

State == {
    "Init", "SwapPointer", "IncreaseRefAgain",
    "IncreaseRef", "DecreaseLocalCounter", "ClearExtraRef",
    "UseObject",
    "DecreaseRef", "DestroyObject", "Terminated"}

TypeOK ==
    /\ objects \in Seq(Object)
    /\ pointer \in DOMAIN objects
    /\ counter \in Nat
    /\ pc \in [Node -> State]
    /\ local_addr \in [Node -> NullAddr]
    /\ last_counter \in [Node -> Nat]


Init ==
    /\ objects = <<[ref |-> 1, extra |-> 0, added |-> FALSE, destroyed |-> 0]>>
    /\ pointer = 1
    /\ counter = 0
    /\ pc = [n \in Node |-> "Init"]
    /\ local_addr = [n \in Node |-> nil]
    /\ last_counter = [n \in Node |-> 0]



goto(n, l) ==
    /\ pc' = [pc EXCEPT ![n] = l]


newObject == [ref |-> 1, extra |-> 0, added |-> FALSE, destroyed |-> 0]

allocNew(n) ==
    /\ objects' = Append(objects, newObject)
    /\ local_addr' = [local_addr EXCEPT ![n] = Len(objects')]


reuseObject(n) ==
    \E addr \in DOMAIN objects:
        /\ objects[addr].destroyed = 1
        /\ objects' = [objects EXCEPT ![addr] = newObject]
        /\ local_addr' = [local_addr EXCEPT ![n] = addr]


AllocateNewObject(n) ==
    /\ pc[n] = "Init"
    /\ goto(n, "SwapPointer")
    /\ \/ allocNew(n)
       \/ reuseObject(n)
    /\ UNCHANGED <<counter, pointer>>
    /\ UNCHANGED last_counter


SwapPointer(n) ==
    /\ pc[n] = "SwapPointer"
    /\ pointer' = local_addr[n]
    /\ local_addr' = [local_addr EXCEPT ![n] = pointer]
    /\ IF counter = 0
        THEN
            /\ goto(n, "DecreaseRef")
            /\ UNCHANGED counter
        ELSE 
            /\ goto(n, "IncreaseRefAgain")
            /\ counter' = 0
    /\ last_counter' = [last_counter EXCEPT ![n] = counter]
    /\ UNCHANGED objects


IncreaseRefAgain(n) ==
    LET
        addr == local_addr[n]
        diff == last_counter[n] - objects[addr].extra
    IN
        /\ pc[n] = "IncreaseRefAgain"
        /\ goto(n, "DecreaseRef")
        /\ objects' = [
            objects EXCEPT ![addr].ref = @ + diff, ![addr].added = TRUE]
        /\ UNCHANGED counter
        /\ UNCHANGED pointer
        /\ UNCHANGED local_addr
        /\ UNCHANGED last_counter


LoadPointer(n) ==
    /\ pc[n] = "Init"
    /\ counter' = counter + 1
    /\ local_addr' = [local_addr EXCEPT ![n] = pointer]
    /\ goto(n, "IncreaseRef")
    /\ UNCHANGED objects
    /\ UNCHANGED pointer
    /\ UNCHANGED last_counter


IncreaseRef(n) ==
    LET
        addr == local_addr[n]
    IN
        /\ pc[n] = "IncreaseRef"
        /\ objects' = [objects EXCEPT ![addr].ref = @ + 1]
        /\ goto(n, "DecreaseLocalCounter")
        /\ UNCHANGED local_addr
        /\ UNCHANGED counter
        /\ UNCHANGED pointer
        /\ UNCHANGED last_counter


DecreaseLocalCounter(n) ==
    /\ pc[n] = "DecreaseLocalCounter"
    /\ IF pointer = local_addr[n]
        THEN
            /\ counter' = counter - 1
            /\ goto(n, "UseObject")
        ELSE
            /\ UNCHANGED counter
            /\ goto(n, "ClearExtraRef")
    /\ UNCHANGED local_addr
    /\ UNCHANGED objects
    /\ UNCHANGED pointer
    /\ UNCHANGED last_counter


ClearExtraRef(n) ==
    LET
        addr == local_addr[n]
    IN
        /\ pc[n] = "ClearExtraRef"
        /\ IF objects[addr].added
            THEN objects' = [
                objects EXCEPT ![addr].ref = @ - 1]
            ELSE objects' = [
                objects EXCEPT ![addr].extra = @ + 1]
        /\ goto(n, "UseObject")
        /\ UNCHANGED local_addr
        /\ UNCHANGED counter
        /\ UNCHANGED pointer
        /\ UNCHANGED last_counter


UseObject(n) ==
    /\ pc[n] = "UseObject"
    /\ goto(n, "DecreaseRef")
    /\ UNCHANGED objects
    /\ UNCHANGED counter
    /\ UNCHANGED pointer
    /\ UNCHANGED local_addr
    /\ UNCHANGED last_counter


DecreaseRef(n) ==
    LET
        addr == local_addr[n]
    IN
        /\ pc[n] = "DecreaseRef"
        /\ objects' = [objects EXCEPT ![addr].ref = @ - 1]
        /\ IF objects'[addr].ref = 0
            THEN goto(n, "DestroyObject")
            ELSE goto(n, "Terminated")
        /\ UNCHANGED local_addr
        /\ UNCHANGED counter
        /\ UNCHANGED pointer
        /\ UNCHANGED last_counter


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
        /\ UNCHANGED last_counter


TerminateCond ==
    /\ \A n \in Node: pc[n] = "Terminated"

Terminated ==
    /\ TerminateCond
    /\ UNCHANGED vars


Next ==
    \/ \E n \in Node:
        \/ AllocateNewObject(n)
        \/ SwapPointer(n)
        \/ IncreaseRefAgain(n)
        \/ LoadPointer(n)
        \/ IncreaseRef(n)
        \/ DecreaseLocalCounter(n)
        \/ ClearExtraRef(n)
        \/ UseObject(n)
        \/ DecreaseRef(n)
        \/ DestroyObject(n)
    \/ Terminated

Spec == Init /\ [][Next]_vars

FairSpec == Spec /\ WF_vars(Next)


FullyDestroyed ==
    LET
        destroyedExceptLast(addr) ==
            addr # pointer => objects[addr].destroyed = 1 /\ objects[addr].ref = 0

        allDestroyed ==
            \A addr \in DOMAIN objects: destroyedExceptLast(addr)
    IN
        TerminateCond => allDestroyed


UseObjectAlwaysValid ==
    LET
        getObj(n) == objects[local_addr[n]]
        notUseAfterFree(n) ==
            /\ getObj(n).destroyed = 0
            /\ getObj(n).ref > 0
    IN
        \A n \in Node: pc[n] = "UseObject" => notUseAfterFree(n)


IncreaseRefMustNotDestroyed ==
    LET
        accessStates(n) == pc[n] = "IncreaseRef"
        getObj(n) == objects[local_addr[n]]
    IN
        \A n \in Node: accessStates(n) => getObj(n).destroyed = 0

AccessStateMustNotDestroyed ==
    LET
        accessStates(n) ==
            \/ pc[n] = "IncreaseRef"
            \/ pc[n] = "IncreaseRefAgain"
            \/ pc[n] = "DecreaseLocalCounter"
            \/ pc[n] = "ClearExtraRef"
            \/ pc[n] = "UseObject"
            \/ pc[n] = "DecreaseRef"
            \/ pc[n] = "DestroyObject"

        getObj(n) == objects[local_addr[n]]
    IN
        \A n \in Node: accessStates(n) => getObj(n).destroyed = 0


AlwaysTerminate == <> TerminateCond


IncreaseRefLeadToUseObject ==
    \A n \in Node:
        pc[n] = "IncreaseRef" ~> pc[n] = "UseObject"


Sym == Permutations(Node)

====

------ MODULE AtomicPtr ----
EXTENDS TLC, Integers, Sequences

CONSTANTS Node, nil

VARIABLES pc, ref_states, pointer, local_ref

vars == <<pc, ref_states, pointer, local_ref>>


RefState == [ref_count: 0..20, is_zero: BOOLEAN, destroyed: 0..30]

State == {
    "Init",
    "LoadPointer", "IncreaseRefCount",
    "UseObject",
    "StartSwapPtr",
    "Decrease", "TryToSetZero", "Destroy",
    "Terminated"
}

NullRefAddr == (DOMAIN ref_states) \union {nil}

TypeOK ==
    /\ pc \in [Node -> State]
    /\ ref_states \in Seq(RefState)
    /\ pointer \in DOMAIN ref_states
    /\ local_ref \in [Node -> NullRefAddr]


Init ==
    /\ \E n0 \in Node:
        /\ pc = [n \in Node |-> IF n = n0 THEN "Decrease" ELSE "Init"]
        /\ local_ref = [n \in Node |-> IF n = n0 THEN 1 ELSE nil]
    /\ ref_states = <<[ref_count |-> 1, is_zero |-> FALSE, destroyed |-> 0]>>
    /\ pointer = 1


goto(n, l) ==
    pc' = [pc EXCEPT ![n] = l]


IncreaseOrStartSwapPtr(n) ==
    /\ pc[n] = "Init"
    /\ \/ goto(n, "LoadPointer")
       \* \/ goto(n, "StartSwapPtr")
    /\ UNCHANGED local_ref
    /\ UNCHANGED pointer
    /\ UNCHANGED ref_states


LoadPointer(n) ==
    /\ pc[n] = "LoadPointer"
    /\ local_ref' = [local_ref EXCEPT ![n] = pointer]
    /\ goto(n, "IncreaseRefCount")
    /\ UNCHANGED ref_states
    /\ UNCHANGED pointer


IncreaseRefCount(n) ==
    LET
        addr == local_ref[n]
        is_zero == ref_states[addr].is_zero
    IN
        /\ pc[n] = "IncreaseRefCount"
        /\ ref_states' = [ref_states EXCEPT ![addr].ref_count = @ + 1]
        /\ IF is_zero
            THEN goto(n, "Terminated")
            ELSE goto(n, "UseObject")
        /\ UNCHANGED local_ref
        /\ UNCHANGED pointer


UseObject(n) ==
    /\ pc[n] = "UseObject"
    /\ goto(n, "Decrease")
    /\ UNCHANGED local_ref
    /\ UNCHANGED pointer
    /\ UNCHANGED ref_states


DecreaseRef(n) ==
    LET
        addr == local_ref[n]
        old_state == ref_states[addr]
        new_count == old_state.ref_count - 1
        new_state == [old_state EXCEPT !.ref_count = new_count]
    IN
        /\ pc[n] = "Decrease"
        /\ ref_states' = [ref_states EXCEPT ![addr] = new_state]
        /\ IF new_count = 0
            THEN goto(n, "TryToSetZero")
            ELSE goto(n, "Terminated")
        /\ UNCHANGED pointer
        /\ UNCHANGED local_ref


TryToSetZero(n) ==
    LET
        addr == local_ref[n]
        old_count == ref_states[addr].ref_count
        old_is_zero == ref_states[addr].is_zero
    IN
        /\ pc[n] = "TryToSetZero"
        /\ IF old_count = 0 /\ old_is_zero = FALSE
            THEN
                /\ ref_states' = [ref_states EXCEPT ![addr].is_zero = TRUE]
                /\ goto(n, "Destroy")
            ELSE
                /\ UNCHANGED ref_states
                /\ goto(n, "Terminated")
        /\ UNCHANGED pointer
        /\ UNCHANGED local_ref


DestroyObject(n) ==
    LET
        addr == local_ref[n]
    IN
        /\ pc[n] = "Destroy"
        /\ goto(n, "Terminated")
        /\ ref_states' = [ref_states EXCEPT ![addr].destroyed = @ + 1]
        /\ UNCHANGED pointer
        /\ UNCHANGED local_ref


TerminateCond ==
    /\ \A n \in Node: pc[n] = "Terminated"

Terminated ==
    /\ TerminateCond
    /\ UNCHANGED vars


Next ==
    \/ \E n \in Node:
        \/ IncreaseOrStartSwapPtr(n)

        \/ LoadPointer(n)
        \/ IncreaseRefCount(n)
        \/ UseObject(n)

        \/ DecreaseRef(n)
        \/ TryToSetZero(n)
        \/ DestroyObject(n)
    \/ Terminated


DestroyOnce ==
    TerminateCond =>
        (\A i \in DOMAIN ref_states: ref_states[i].destroyed = 1)

====
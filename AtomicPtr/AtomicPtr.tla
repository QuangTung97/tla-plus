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
    "Decrease", "TryToSetZero", "Destroy",
    "StartSwapPtr", "UpdatePointer",
    "Terminated"
}

NullRefAddr == (DOMAIN ref_states) \union {nil}

TypeOK ==
    /\ pc \in [Node -> State]
    /\ ref_states \in Seq(RefState)
    /\ pointer \in DOMAIN ref_states
    /\ local_ref \in [Node -> NullRefAddr]


Init ==
    /\ pc = [n \in Node |-> "Init"]
    /\ local_ref = [n \in Node |-> nil]
    /\ ref_states = <<[ref_count |-> 1, is_zero |-> FALSE, destroyed |-> 0]>>
    /\ pointer = 1


goto(n, l) ==
    pc' = [pc EXCEPT ![n] = l]


LoadPointerOrSwapPtr(n) ==
    /\ pc[n] = "Init"
    /\ \/ goto(n, "LoadPointer")
       \/ goto(n, "StartSwapPtr")
    /\ UNCHANGED pointer
    /\ UNCHANGED ref_states
    /\ UNCHANGED local_ref


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
            THEN goto(n, "LoadPointer")
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


StartSwapPtr(n) ==
    LET
        new_state == [ref_count |-> 1, is_zero |-> FALSE, destroyed |-> 0]
        new_addr == Len(ref_states) + 1
    IN
        /\ pc[n] = "StartSwapPtr"
        /\ goto(n, "UpdatePointer")
        /\ ref_states' = Append(ref_states, new_state)
        /\ local_ref' = [local_ref EXCEPT ![n] = new_addr]
        /\ UNCHANGED pointer


UpdatePointer(n) ==
    LET
        addr == local_ref[n]
    IN
        /\ pc[n] = "UpdatePointer"
        /\ goto(n, "Decrease")
        /\ pointer' = addr
        /\ local_ref' = [local_ref EXCEPT ![n] = pointer]
        /\ UNCHANGED ref_states


TerminateCond ==
    /\ \A n \in Node: pc[n] = "Terminated"

Terminated ==
    /\ TerminateCond
    /\ UNCHANGED vars


Next ==
    \/ \E n \in Node:
        \/ LoadPointerOrSwapPtr(n)

        \/ LoadPointer(n)
        \/ IncreaseRefCount(n)
        \/ UseObject(n)

        \/ DecreaseRef(n)
        \/ TryToSetZero(n)
        \/ DestroyObject(n)

        \/ StartSwapPtr(n)
        \/ UpdatePointer(n)
    \/ Terminated


Spec == Init /\ [][Next]_vars

FairSpec == Spec /\ WF_vars(Next)


nonPrimaryRefStateDestroyed(i)==
    i # pointer => ref_states[i].destroyed = 1

DestroyOnce ==
    TerminateCond =>
        (\A i \in DOMAIN ref_states: nonPrimaryRefStateDestroyed(i))


UseStateNotDestroyed ==
    \A n \in Node:
        pc[n] = "UseObject" => ref_states[local_ref[n]].destroyed = 0


AlwaysTerminate == <> TerminateCond


IncreaseAlwaysLeadToUsable ==
    \A n \in Node:
        pc[n] = "IncreaseRefCount" ~> pc[n] = "UseObject"

====
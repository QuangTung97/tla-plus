------ MODULE PandoraWorkspace ----
EXTENDS TLC, Sequences, Naturals

CONSTANTS Node, Key, nil

VARIABLES
    mem, mem_state, disk,
    pc, local_state

local_vars == <<
    pc, local_state
>>

vars == <<mem, mem_state, disk, local_vars>>

-------------------------------------------------------

MemState == [
    key: Key,
    ready: BOOLEAN,
    update: 0..10
]

NullMemState == DOMAIN(mem_state) \union {nil}

DiskState == [
    ready: {TRUE}
]

NullDiskState == DiskState \union {nil}

PC == {"Init", "CreateKeyOnDisk", "Terminated"}

-------------------------------------------------------

TypeOK ==
    /\ mem \in [Key -> NullMemState]
    /\ mem_state \in Seq(MemState)
    /\ disk \in [Key -> NullDiskState]

    /\ pc \in [Node -> PC]
    /\ local_state \in [Node -> NullMemState]

Init ==
    /\ mem = [k \in Key |-> nil]
    /\ mem_state = <<>>
    /\ disk = [k \in Key |-> nil]

    /\ pc = [n \in Node |-> "Init"]
    /\ local_state = [n \in Node |-> nil]

-------------------------------------------------------

goto(n, l) ==
    pc' = [pc EXCEPT ![n] = l]

update_local(var, n, new_val) ==
    var' = [var EXCEPT ![n] = new_val]


CreateNewKey(n, k) ==
    LET
        new_state == [
            key |-> k,
            ready |-> FALSE,
            update |-> 0
        ]

        addr == Len(mem_state')
    IN
    /\ pc[n] = "Init"
    /\ mem[k] = nil

    /\ goto(n, "CreateKeyOnDisk")
    /\ mem_state' = Append(mem_state, new_state)
    /\ mem' = [mem EXCEPT ![k] = addr]
    /\ update_local(local_state, n, addr)

    /\ UNCHANGED disk


CreateKeyOnDisk(n) ==
    LET
        addr == local_state[n]
        state == mem_state[addr]
        k == state.key

        when_success ==
            /\ goto(n, "Terminated")
            /\ mem_state' = [mem_state EXCEPT ![addr].ready = TRUE]
            /\ disk' = [disk EXCEPT ![k] = [ready |-> TRUE]]
            /\ update_local(local_state, n, nil)
    IN
    /\ pc[n] = "CreateKeyOnDisk"
    /\ \/ when_success

    /\ UNCHANGED mem

-------------------------------------------------------

TerminateCond ==
    /\ \A n \in Node: pc[n] = "Terminated"

Terminated ==
    /\ TerminateCond
    /\ UNCHANGED vars


Next ==
    \/ \E n \in Node, k \in Key:
        \/ CreateNewKey(n, k)
    \/ \E n \in Node:
        \/ CreateKeyOnDisk(n)
    \/ Terminated

Spec == Init /\ [][Next]_vars

====

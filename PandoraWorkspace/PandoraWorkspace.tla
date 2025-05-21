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
    status: {"WriteLock", "NoLock"},
    deleted: BOOLEAN,
    update: 0..10
]

NullMemState == DOMAIN(mem_state) \union {nil}

DiskState == [
    ready: {TRUE}
]

NullDiskState == DiskState \union {nil}

PC == {
    "Init", "CreateKeyOnDisk", "RemoveFromMem",
    "DoActualDelete",
    "Terminated"
}

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
            status |-> "WriteLock", \* Two phase locking here
            deleted |-> FALSE,
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
            /\ disk' = [disk EXCEPT ![k] = [ready |-> TRUE]]
            \* release lock
            /\ mem_state' = [mem_state EXCEPT ![addr].status = "NoLock"]
            /\ update_local(local_state, n, nil)

        when_fail ==
            /\ goto(n, "RemoveFromMem")
            /\ mem_state' = [mem_state EXCEPT
                    ![addr].deleted = TRUE,
                    ![addr].status = "NoLock"
                ]
            /\ UNCHANGED local_state
            /\ UNCHANGED disk
    IN
    /\ pc[n] = "CreateKeyOnDisk"
    /\ \/ when_success
       \/ when_fail

    /\ UNCHANGED mem


RemoveFromMem(n) ==
    LET
        addr == local_state[n]
        state == mem_state[addr]
        k == state.key
    IN
    /\ pc[n] = "RemoveFromMem"
    /\ goto(n, "Terminated")

    /\ mem' = [mem EXCEPT ![k] = nil]
    /\ update_local(local_state, n, nil)

    /\ UNCHANGED mem_state
    /\ UNCHANGED disk


CheckToDelete(n, k) ==
    /\ pc[n] = "Init"
    /\ mem[k] # nil

    /\ goto(n, "DoActualDelete")
    /\ update_local(local_state, n, mem[k])

    /\ UNCHANGED disk
    /\ UNCHANGED mem
    /\ UNCHANGED mem_state


DoActualDelete(n) ==
    LET
        addr == local_state[n]
        k == mem_state[addr].key

        do_nothing ==
            /\ goto(n, "Terminated")
            /\ UNCHANGED disk
            /\ UNCHANGED mem_state

        do_delete ==
            /\ goto(n, "RemoveFromMem")
            /\ mem_state' = [mem_state EXCEPT ![addr].deleted = TRUE]
            /\ disk' = [disk EXCEPT ![k] = nil]
    IN
    /\ pc[n] = "DoActualDelete"
    /\ mem_state[addr].status = "NoLock" \* wait for write lock

    /\ IF mem_state[addr].deleted
        THEN do_nothing
        ELSE do_delete

    /\ UNCHANGED mem
    /\ UNCHANGED local_state


-------------------------------------------------------

TerminateCond ==
    /\ \A n \in Node: pc[n] = "Terminated"

Terminated ==
    /\ TerminateCond
    /\ UNCHANGED vars


Next ==
    \/ \E n \in Node, k \in Key:
        \/ CreateNewKey(n, k)
        \/ CheckToDelete(n, k)
    \/ \E n \in Node:
        \/ CreateKeyOnDisk(n)
        \/ RemoveFromMem(n)
        \/ DoActualDelete(n)
    \/ Terminated

Spec == Init /\ [][Next]_vars

-------------------------------------------------------

memStateDeletedCond(addr) ==
    LET
        k == mem_state[addr].key
    IN
    mem_state[addr].deleted <=> mem[k] # addr

memMatchDisk ==
    LET
        mem_keys == {k \in Key: mem[k] # nil}
        disk_keys == {k \in Key: disk[k] # nil}
    IN
        mem_keys = disk_keys

WhenTerminatedInv ==
    TerminateCond =>
        /\ \A addr \in DOMAIN(mem_state):
                /\ memStateDeletedCond(addr)
                /\ mem_state[addr].status = "NoLock"
        /\ memMatchDisk

====

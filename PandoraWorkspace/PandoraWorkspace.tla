------ MODULE PandoraWorkspace ----
EXTENDS TLC, Sequences, Naturals, FiniteSets

CONSTANTS Node, Key, nil

VARIABLES
    mem, global_state, mem_status, disk,
    pc, local_addr, local_new_addr

local_vars == <<
    pc, local_addr, local_new_addr
>>

vars == <<mem, global_state, mem_status, disk, local_vars>>

-------------------------------------------------------

DeleteKey == Key \union ({"deleted"} \X Key)

MemState == [
    key: DeleteKey,
    status: {"WriteLock", "ReadLock", "NoLock"},
    deleted: BOOLEAN,
    read_count: 0..10
]

NullAddr == DOMAIN(global_state) \union {nil}

MemStatus == {"Creating", "Ready", "Deleting"}

NullMemStatus == MemStatus \union {nil}

DiskState == [
    ready: {TRUE}
]

NullDiskState == DiskState \union {nil}

PC == {
    "Init",
    "CreateKeyOnDisk", "UpdateStatusToReady",
    "RemoveFromMem",
    "SoftDeleteDoLock", "SoftDelete", "SoftDeleteFinish",
    "HardDeleteDoLock", "HardDelete",
    "RecoverDoLock", "Recover", "RecoverFinish", "RecoverRollback",
    "GetKey",
    "Terminated"
}

-------------------------------------------------------

TypeOK ==
    /\ mem \in [DeleteKey -> NullAddr]
    /\ global_state \in Seq(MemState)
    /\ mem_status \in [DeleteKey -> NullMemStatus]
    /\ disk \in [DeleteKey -> NullDiskState]

    /\ pc \in [Node -> PC]
    /\ local_addr \in [Node -> NullAddr]
    /\ local_new_addr \in [Node -> NullAddr]

Init ==
    /\ mem = [k \in DeleteKey |-> nil]
    /\ global_state = <<>>
    /\ mem_status = [k \in DeleteKey |-> nil]
    /\ disk = [k \in DeleteKey |-> nil]

    /\ pc = [n \in Node |-> "Init"]
    /\ local_addr = [n \in Node |-> nil]
    /\ local_new_addr = [n \in Node |-> nil]

-------------------------------------------------------

goto(n, l) ==
    pc' = [pc EXCEPT ![n] = l]

update_local(var, n, new_val) ==
    var' = [var EXCEPT ![n] = new_val]

update_status_to_creating(old_status, k) ==
    [old_status EXCEPT ![k] = "Creating"]


CreateNewKey(n, k) ==
    LET
        new_state == [
            key |-> k,
            status |-> "WriteLock", \* Two phase locking here
            deleted |-> FALSE,
            read_count |-> 0
        ]

        addr == Len(global_state')
    IN
    /\ pc[n] = "Init"
    /\ mem[k] = nil

    /\ goto(n, "CreateKeyOnDisk")
    /\ global_state' = Append(global_state, new_state)
    /\ mem' = [mem EXCEPT ![k] = addr]
    /\ mem_status' = update_status_to_creating(mem_status, k)
    /\ update_local(local_addr, n, addr)

    /\ UNCHANGED local_new_addr
    /\ UNCHANGED disk


CreateKeyOnDisk(n) ==
    LET
        addr == local_addr[n]
        state == global_state[addr]
        k == state.key

        when_success ==
            /\ goto(n, "UpdateStatusToReady")
            /\ disk' = [disk EXCEPT ![k] = [ready |-> TRUE]]
            /\ global_state' = [global_state EXCEPT ![addr].status = "NoLock"]
            /\ UNCHANGED local_addr

        when_fail ==
            /\ goto(n, "RemoveFromMem")
            /\ global_state' = [global_state EXCEPT
                    ![addr].deleted = TRUE,
                    ![addr].status = "NoLock"
                ]
            /\ UNCHANGED local_addr
            /\ UNCHANGED disk
    IN
    /\ pc[n] = "CreateKeyOnDisk"
    /\ \/ when_success
       \/ when_fail

    /\ UNCHANGED local_new_addr
    /\ UNCHANGED mem
    /\ UNCHANGED mem_status


UpdateStatusToReady(n) ==
    LET
        addr == local_addr[n]
        k == global_state[addr].key
    IN
    /\ pc[n] = "UpdateStatusToReady"
    /\ goto(n, "Terminated")

    /\ mem_status' = [mem_status EXCEPT ![k] = "Ready"]
    /\ update_local(local_addr, n, nil)
    /\ UNCHANGED mem

    /\ UNCHANGED local_new_addr
    /\ UNCHANGED global_state
    /\ UNCHANGED disk


RemoveFromMem(n) ==
    LET
        addr == local_addr[n]
        state == global_state[addr]
        k == state.key
    IN
    /\ pc[n] = "RemoveFromMem"
    /\ goto(n, "Terminated")

    /\ mem' = [mem EXCEPT ![k] = nil]
    /\ mem_status' = [mem_status EXCEPT ![k] = nil]
    /\ update_local(local_addr, n, nil)

    /\ UNCHANGED local_new_addr
    /\ UNCHANGED global_state
    /\ UNCHANGED disk

-------------------------------------------------------

update_status_to_deleting(old_status, k) ==
    [old_status EXCEPT ![k] = "Deleting"]


SoftDeleteOnMem(n, k) ==
    LET
        new_key == <<"deleted", k>>

        after_delete == update_status_to_deleting(mem_status, k)
        final_status == update_status_to_creating(after_delete, new_key)

        new_state == [
            key |-> new_key,
            status |-> "WriteLock",
            deleted |-> FALSE,
            read_count |-> 0
        ]

        old_addr == mem[k]
        new_addr == Len(global_state')
    IN
    /\ pc[n] = "Init"
    /\ goto(n, "SoftDeleteDoLock")

    /\ mem[k] # nil
    /\ mem_status[k] = "Ready"
    /\ mem[new_key] = nil \* Special Condition

    /\ mem_status' = final_status
    /\ global_state' = Append(global_state, new_state)
    /\ mem' = [mem EXCEPT ![new_key] = new_addr]

    /\ update_local(local_addr, n, old_addr)
    /\ update_local(local_new_addr, n, new_addr)

    /\ UNCHANGED disk


memUnchanged ==
    /\ UNCHANGED <<local_addr, local_new_addr>>
    /\ UNCHANGED mem
    /\ UNCHANGED mem_status


obtainWriteLock(addr) ==
    /\ global_state[addr].status = "NoLock"
    /\ global_state' = [global_state EXCEPT ![addr].status = "WriteLock"]


SoftDeleteDoLock(n) ==
    LET
        addr == local_addr[n]
    IN
    /\ pc[n] = "SoftDeleteDoLock"
    /\ goto(n, "SoftDelete")

    /\ obtainWriteLock(addr)

    /\ UNCHANGED disk
    /\ memUnchanged


SoftDelete(n) == \* TODO on fail
    LET
        old_addr == local_addr[n]
        old_state == global_state[old_addr]
        k == old_state.key

        new_addr == local_new_addr[n]

        new_key == <<"deleted", k>>
    IN
    /\ pc[n] = "SoftDelete"
    /\ goto(n, "SoftDeleteFinish")

    /\ global_state' = [global_state EXCEPT
            ![old_addr].deleted = TRUE,
            ![old_addr].status = "NoLock",
            ![new_addr].status = "NoLock"
        ]

    /\ disk' = [disk EXCEPT
            ![k] = nil,
            ![new_key] = [ready |-> TRUE]
        ]

    /\ UNCHANGED <<local_addr, local_new_addr>>
    /\ UNCHANGED mem
    /\ UNCHANGED mem_status


SoftDeleteFinish(n) ==
    LET
        old_addr == local_addr[n]
        old_state == global_state[old_addr]
        k == old_state.key
        new_key == <<"deleted", k>>
    IN
    /\ pc[n] = "SoftDeleteFinish"
    /\ goto(n, "Terminated")

    /\ mem' = [mem EXCEPT ![k] = nil]
    /\ mem_status' = [mem_status EXCEPT
            ![k] = nil,
            ![new_key] = "Ready"
        ]

    /\ update_local(local_addr, n, nil)
    /\ update_local(local_new_addr, n, nil)

    /\ UNCHANGED global_state
    /\ UNCHANGED disk

-------------------------------------------------------

HardDeleteOnMem(n, k) ==
    LET
        new_key == <<"deleted", k>>
    IN
    /\ pc[n] = "Init"
    /\ mem[new_key] # nil
    /\ mem_status[new_key] = "Ready"

    /\ goto(n, "HardDeleteDoLock")
    /\ mem_status' = [mem_status EXCEPT ![new_key] = "Deleting"]

    /\ update_local(local_addr, n, mem[new_key])
    /\ UNCHANGED local_new_addr

    /\ UNCHANGED global_state
    /\ UNCHANGED mem
    /\ UNCHANGED disk


HardDeleteDoLock(n) ==
    LET
        addr == local_addr[n]
    IN
    /\ pc[n] = "HardDeleteDoLock"

    /\ goto(n, "HardDelete")
    /\ obtainWriteLock(addr)

    /\ UNCHANGED disk
    /\ memUnchanged


HardDelete(n) ==
    LET
        addr == local_addr[n]
        k == global_state[addr].key
    IN
    /\ pc[n] = "HardDelete"
    /\ goto(n, "RemoveFromMem")

    /\ disk' = [disk EXCEPT ![k] = nil]
    /\ global_state' = [global_state EXCEPT
            ![addr].deleted = TRUE,
            ![addr].status = "NoLock"
        ]

    /\ UNCHANGED <<local_addr, local_new_addr>>
    /\ UNCHANGED <<mem, mem_status>>


-------------------------------------------------------

RecoverOnMem(n, k) ==
    LET
        old_key == <<"deleted", k>>

        new_state == [
            key |-> k,
            status |-> "WriteLock",
            deleted |-> FALSE,
            read_count |-> 0
        ]

        new_addr == Len(global_state')
    IN
    /\ pc[n] = "Init"
    /\ mem[old_key] # nil
    /\ mem_status[old_key] = "Ready"
    /\ mem[k] = nil

    /\ goto(n, "RecoverDoLock")
    /\ global_state' = Append(global_state, new_state)
    /\ mem' = [mem EXCEPT ![k] = new_addr]
    /\ mem_status' = [mem_status EXCEPT
            ![old_key] = "Deleting",
            ![k] = "Creating"
        ]

    /\ update_local(local_addr, n, mem[old_key])
    /\ update_local(local_new_addr, n, new_addr)

    /\ UNCHANGED disk


RecoverDoLock(n) ==
    LET
        addr == local_addr[n]
    IN
    /\ pc[n] = "RecoverDoLock"
    /\ goto(n, "Recover")

    /\ obtainWriteLock(addr)

    /\ UNCHANGED disk
    /\ memUnchanged


Recover(n) ==
    LET
        old_addr == local_addr[n]
        new_addr == local_new_addr[n]

        old_key == global_state[old_addr].key
        new_key == global_state[new_addr].key

        when_success ==
            /\ goto(n, "RecoverFinish")
            /\ disk' = [disk EXCEPT
                    ![old_key] = nil,
                    ![new_key] = [ready |-> TRUE]
                ]
            /\ global_state' = [global_state EXCEPT
                    ![old_addr].deleted = TRUE,
                    ![old_addr].status = "NoLock",
                    ![new_addr].status = "NoLock"
                ]

        when_fail ==
            /\ goto(n, "RecoverRollback")
            /\ global_state' = [global_state EXCEPT
                    ![old_addr].status = "NoLock",
                    ![new_addr].status = "NoLock",
                    ![new_addr].deleted = TRUE
                ]
            /\ UNCHANGED disk
    IN
    /\ pc[n] = "Recover"
    /\ \/ when_success
       \/ when_fail

    /\ memUnchanged


RecoverFinish(n) ==
    LET
        old_addr == local_addr[n]
        new_addr == local_new_addr[n]

        old_key == global_state[old_addr].key
        new_key == global_state[new_addr].key
    IN
    /\ pc[n] = "RecoverFinish"
    /\ goto(n, "Terminated")

    /\ mem' = [mem EXCEPT ![old_key] = nil]
    /\ mem_status' = [mem_status EXCEPT
            ![old_key] = nil,
            ![new_key] = "Ready"
        ]

    /\ update_local(local_addr, n, nil)
    /\ update_local(local_new_addr, n, nil)

    /\ UNCHANGED global_state
    /\ UNCHANGED disk


RecoverRollback(n) ==
    LET
        old_addr == local_addr[n]
        new_addr == local_new_addr[n]

        old_key == global_state[old_addr].key
        new_key == global_state[new_addr].key
    IN
    /\ pc[n] = "RecoverRollback"
    /\ goto(n, "Terminated")

    /\ mem' = [mem EXCEPT ![new_key] = nil]
    /\ mem_status' = [mem_status EXCEPT
            ![old_key] = "Ready",
            ![new_key] = nil
        ]

    /\ update_local(local_addr, n, nil)
    /\ update_local(local_new_addr, n, nil)

    /\ UNCHANGED global_state
    /\ UNCHANGED disk

-------------------------------------------------------

getKeyUnchanged ==
    /\ UNCHANGED global_state
    /\ UNCHANGED mem
    /\ UNCHANGED mem_status
    /\ UNCHANGED disk
    /\ UNCHANGED local_new_addr

GetKeyOnMem(n, k) ==
    LET
        when_found ==
            /\ mem[k] # nil
            /\ goto(n, "GetKey")
            /\ update_local(local_addr, n, mem[k])
    IN
    /\ pc[n] = "Init"
    /\ \/ when_found

    /\ getKeyUnchanged


GetKeyFound(n) ==
    LET
        addr == local_addr[n]
        state == global_state[addr]
        k == state.key
    IN
    /\ pc[n] = "GetKey"
    /\ state.status = "NoLock"
    /\ ~state.deleted

    /\ goto(n, "Terminated")
    /\ update_local(local_addr, n, nil)

    /\ getKeyUnchanged


GetKeyNotFound(n) ==
    LET
        addr == local_addr[n]
        state == global_state[addr]
        k == state.key
    IN
    /\ pc[n] = "GetKey"
    /\ state.status = "NoLock"
    /\ state.deleted

    /\ goto(n, "Terminated")
    /\ update_local(local_addr, n, nil)

    /\ getKeyUnchanged

-------------------------------------------------------

TerminateCond ==
    /\ \A n \in Node: pc[n] = "Terminated"

Terminated ==
    /\ TerminateCond
    /\ UNCHANGED vars


Next ==
    \/ \E n \in Node, k \in Key:
        \/ CreateNewKey(n, k)
        \/ SoftDeleteOnMem(n, k)
        \/ HardDeleteOnMem(n, k)
        \/ RecoverOnMem(n, k)
        \/ GetKeyOnMem(n, k)
    \/ \E n \in Node:
        \/ CreateKeyOnDisk(n)
        \/ UpdateStatusToReady(n)
        \/ RemoveFromMem(n)

        \/ SoftDeleteDoLock(n)
        \/ SoftDelete(n)
        \/ SoftDeleteFinish(n)

        \/ HardDeleteDoLock(n)
        \/ HardDelete(n)

        \/ RecoverDoLock(n)
        \/ Recover(n)
        \/ RecoverFinish(n)
        \/ RecoverRollback(n)

        \/ GetKeyFound(n)
        \/ GetKeyNotFound(n)
    \/ Terminated

Spec == Init /\ [][Next]_vars

-------------------------------------------------------

memStateDeletedCond(addr) ==
    LET
        k == global_state[addr].key
    IN
    global_state[addr].deleted <=> mem[k] # addr

memMatchDisk ==
    LET
        mem_keys == {k \in DeleteKey: mem[k] # nil}
        disk_keys == {k \in DeleteKey: disk[k] # nil}
    IN
        mem_keys = disk_keys

memStatusReadyOrNil ==
    \A k \in DeleteKey:
        \/ mem_status[k] = nil
        \/ mem_status[k] = "Ready"

localVarsAreNil ==
    \A n \in Node:
        /\ local_addr[n] = nil
        /\ local_new_addr[n] = nil

WhenTerminatedGlobalStateInv ==
    TerminateCond =>
        \A addr \in DOMAIN(global_state):
            /\ memStateDeletedCond(addr)
            /\ global_state[addr].status = "NoLock"

WhenTerminatedMemMatchDiskInv ==
    TerminateCond => memMatchDisk

WhenTerminatedMemStatusInv ==
    TerminateCond => memStatusReadyOrNil

WhenTerminatedLocalVarsInv ==
    TerminateCond => localVarsAreNil


MemStatusInv ==
    \A k \in DeleteKey:
        mem_status[k] # nil <=> mem[k] # nil


MustNotConcurrentWriteToDisk ==
    LET
        writing_to_disk(n) ==
            \/ ENABLED CreateKeyOnDisk(n)
            \/ ENABLED SoftDelete(n)
            \/ ENABLED Recover(n)

        writing_set == {n \in Node: writing_to_disk(n)}

        reading_set == {n \in Node: ENABLED GetKeyFound(n)}
    IN
        /\ Cardinality(writing_set) <= 1
        /\ \/ writing_set = {}
           \/ reading_set = {}


MustNotConcurrentWriteToDiskHardDelete ==
    LET
        writing_to_disk(n) ==
            \/ ENABLED SoftDelete(n)
            \/ ENABLED Recover(n)
            \/ ENABLED HardDelete(n)

        writing_set == {n \in Node: writing_to_disk(n)}

        reading_set == {n \in Node: ENABLED GetKeyFound(n)}
    IN
        /\ Cardinality(writing_set) <= 1


CanNotBothGetFoundAndNotFound ==
    \A n \in Node:
        \/ ~(ENABLED GetKeyFound(n))
        \/ ~(ENABLED GetKeyNotFound(n))


ReverseCond ==
    \A n \in Node: ~(ENABLED HardDelete(n))

====

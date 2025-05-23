------ MODULE PandoraWorkspace ----
EXTENDS TLC, Sequences, Naturals, FiniteSets

CONSTANTS Node, Key, nil

VARIABLES
    mem, global_state, mem_status, added_keys, deleted_keys, disk,
    pc, local_addr, local_new_addr,
    job_pc, job_mem_keys, job_disk_keys, job_loading

local_vars == <<
    pc, local_addr, local_new_addr
>>

job_vars == <<
    job_pc, job_mem_keys, job_disk_keys, job_loading
>>

vars == <<
    mem, global_state, mem_status, added_keys, deleted_keys, disk,
    local_vars, job_vars
>>

-------------------------------------------------------

DeleteKey == Key \union ({"deleted"} \X Key)

MemState == [
    key: DeleteKey,
    status: {"WriteLock", "NoLock"},
    deleted: BOOLEAN
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

JobPC == {
    "Init", "JobLoadDisk",
    "JobDeleteKey", "JobInsertKey", "Terminated"
}

-------------------------------------------------------

TypeOK ==
    /\ mem \in [DeleteKey -> NullAddr]
    /\ global_state \in Seq(MemState)
    /\ mem_status \in [DeleteKey -> NullMemStatus]
    /\ added_keys \subseteq DeleteKey
    /\ deleted_keys \subseteq DeleteKey
    /\ disk \in [DeleteKey -> NullDiskState]

    /\ pc \in [Node -> PC]
    /\ local_addr \in [Node -> NullAddr]
    /\ local_new_addr \in [Node -> NullAddr]

    /\ job_pc \in JobPC
    /\ job_mem_keys \subseteq DeleteKey
    /\ job_disk_keys \subseteq DeleteKey
    /\ job_loading \in BOOLEAN

Init ==
    /\ mem = [k \in DeleteKey |-> nil]
    /\ global_state = <<>>
    /\ mem_status = [k \in DeleteKey |-> nil]
    /\ added_keys = {}
    /\ deleted_keys = {}
    /\ disk = [k \in DeleteKey |-> nil]

    /\ pc = [n \in Node |-> "Init"]
    /\ local_addr = [n \in Node |-> nil]
    /\ local_new_addr = [n \in Node |-> nil]

    /\ job_pc = "Init"
    /\ job_mem_keys = {}
    /\ job_disk_keys = {}
    /\ job_loading = FALSE

-------------------------------------------------------

goto(n, l) ==
    pc' = [pc EXCEPT ![n] = l]

update_local(var, n, new_val) ==
    var' = [var EXCEPT ![n] = new_val]

update_status_to_creating(old_status, k) ==
    [old_status EXCEPT ![k] = "Creating"]


jobKeysUnchanged ==
    /\ UNCHANGED added_keys
    /\ UNCHANGED deleted_keys

addToAddedKeys(k) ==
    IF job_loading
        THEN added_keys' = added_keys \union {k}
        ELSE UNCHANGED added_keys

addToDeletedKeys(k) ==
    IF job_loading
        THEN deleted_keys' = deleted_keys \union {k}
        ELSE UNCHANGED deleted_keys


CreateNewKey(n, k) ==
    LET
        new_state == [
            key |-> k,
            status |-> "WriteLock", \* Two phase locking here
            deleted |-> FALSE
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
    /\ UNCHANGED job_vars
    /\ jobKeysUnchanged


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
    /\ UNCHANGED job_vars
    /\ jobKeysUnchanged


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
    /\ addToAddedKeys(k)

    /\ UNCHANGED local_new_addr
    /\ UNCHANGED global_state
    /\ UNCHANGED disk
    /\ UNCHANGED job_vars
    /\ UNCHANGED deleted_keys


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
    /\ addToDeletedKeys(k)

    /\ UNCHANGED local_new_addr
    /\ UNCHANGED global_state
    /\ UNCHANGED disk
    /\ UNCHANGED job_vars
    /\ UNCHANGED added_keys

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
            deleted |-> FALSE
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
    /\ UNCHANGED job_vars
    /\ jobKeysUnchanged


memUnchanged ==
    /\ UNCHANGED <<local_addr, local_new_addr>>
    /\ UNCHANGED mem
    /\ UNCHANGED mem_status
    /\ UNCHANGED job_vars
    /\ jobKeysUnchanged


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
    /\ UNCHANGED job_vars
    /\ jobKeysUnchanged


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
    /\ addToAddedKeys(new_key)
    /\ addToDeletedKeys(k)

    /\ update_local(local_addr, n, nil)
    /\ update_local(local_new_addr, n, nil)

    /\ UNCHANGED global_state
    /\ UNCHANGED disk
    /\ UNCHANGED job_vars

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
    /\ UNCHANGED job_vars
    /\ jobKeysUnchanged


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
    /\ UNCHANGED job_vars
    /\ jobKeysUnchanged


-------------------------------------------------------

RecoverOnMem(n, k) ==
    LET
        old_key == <<"deleted", k>>

        new_state == [
            key |-> k,
            status |-> "WriteLock",
            deleted |-> FALSE
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
    /\ UNCHANGED job_vars
    /\ jobKeysUnchanged


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
    /\ addToAddedKeys(new_key)
    /\ addToDeletedKeys(old_key)

    /\ update_local(local_addr, n, nil)
    /\ update_local(local_new_addr, n, nil)

    /\ UNCHANGED global_state
    /\ UNCHANGED disk
    /\ UNCHANGED job_vars


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
    /\ UNCHANGED job_vars
    /\ jobKeysUnchanged

-------------------------------------------------------

getKeyUnchanged ==
    /\ UNCHANGED global_state
    /\ UNCHANGED mem
    /\ UNCHANGED mem_status
    /\ UNCHANGED disk
    /\ UNCHANGED local_new_addr
    /\ UNCHANGED job_vars
    /\ jobKeysUnchanged

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

jobUnchanged ==
    /\ UNCHANGED disk
    /\ UNCHANGED local_vars


JobStartLoading ==
    LET
        mem_keys == {k \in DeleteKey: mem[k] # nil}
    IN
    /\ job_pc = "Init"
    /\ job_pc' = "JobLoadDisk"
    /\ job_loading' = TRUE
    /\ job_mem_keys' = mem_keys

    /\ UNCHANGED job_disk_keys
    /\ UNCHANGED global_state
    /\ UNCHANGED <<mem, mem_status>>
    /\ jobKeysUnchanged
    /\ jobUnchanged


JobLoadDisk ==
    LET
        disk_keys == {k \in DeleteKey: disk[k] # nil}
    IN
    /\ job_pc = "JobLoadDisk"
    /\ job_pc' = "JobDeleteKey"
    /\ job_disk_keys' = disk_keys

    /\ UNCHANGED job_loading
    /\ UNCHANGED global_state
    /\ UNCHANGED <<mem, mem_status>>
    /\ UNCHANGED job_mem_keys
    /\ jobKeysUnchanged
    /\ jobUnchanged


jobNeedDeleteSet == (job_mem_keys \ job_disk_keys)

JobDeleteKey(k) ==
    LET
        delete_cond ==
            /\ mem_status[k] = "Ready"
            /\ k \notin added_keys

        do_delete ==
            /\ UNCHANGED job_pc
            /\ mem' = [mem EXCEPT ![k] = nil]
            /\ mem_status' = [mem_status EXCEPT ![k] = nil]
            /\ global_state' = [global_state EXCEPT
                    ![mem[k]].deleted = TRUE
                ]

        do_nothing ==
            /\ UNCHANGED job_pc
            /\ UNCHANGED <<mem, mem_status>>
            /\ UNCHANGED global_state
    IN
    /\ job_pc = "JobDeleteKey"
    /\ k \in jobNeedDeleteSet
    /\ job_mem_keys' = job_mem_keys \ {k}

    /\ IF delete_cond
        THEN do_delete
        ELSE do_nothing

    /\ UNCHANGED job_loading
    /\ UNCHANGED job_disk_keys
    /\ jobKeysUnchanged
    /\ jobUnchanged


JobDeleteFinish ==
    /\ job_pc = "JobDeleteKey"
    /\ jobNeedDeleteSet = {}

    /\ job_pc' = "JobInsertKey"
    /\ job_mem_keys' = {}

    /\ UNCHANGED job_loading
    /\ UNCHANGED job_disk_keys
    /\ UNCHANGED global_state
    /\ UNCHANGED <<mem, mem_status>>
    /\ jobKeysUnchanged
    /\ jobUnchanged


JobInsertKey(k) ==
    LET
        new_state == [
            key |-> k,
            status |-> "NoLock",
            deleted |-> FALSE
        ]
        addr == Len(global_state')

        insert_cond ==
            /\ mem[k] = nil
            /\ k \notin deleted_keys

        when_insert ==
            /\ global_state' = Append(global_state, new_state)
            /\ mem' = [mem EXCEPT ![k] = addr]
            /\ mem_status' = [mem_status EXCEPT ![k] = "Ready"]

        when_nothing ==
            /\ UNCHANGED global_state
            /\ UNCHANGED <<mem, mem_status>>
    IN
    /\ job_pc = "JobInsertKey"
    /\ k \in job_disk_keys

    /\ job_disk_keys' = job_disk_keys \ {k}
    /\ IF insert_cond
        THEN when_insert
        ELSE when_nothing

    /\ UNCHANGED job_mem_keys
    /\ UNCHANGED job_pc
    /\ UNCHANGED job_loading
    /\ jobKeysUnchanged
    /\ jobUnchanged


JobInsertFinish ==
    /\ job_pc = "JobInsertKey"
    /\ job_disk_keys = {}

    /\ job_pc' = "Terminated"
    /\ job_loading' = FALSE
    /\ added_keys' = {}
    /\ deleted_keys' = {}

    /\ UNCHANGED job_mem_keys
    /\ UNCHANGED job_disk_keys
    /\ UNCHANGED global_state
    /\ UNCHANGED <<mem, mem_status>>
    /\ jobUnchanged

-------------------------------------------------------

TerminateCond ==
    /\ \A n \in Node: pc[n] = "Terminated"
    /\ job_pc = "Terminated"

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

    \/ JobStartLoading
    \/ JobLoadDisk
    \/ \E k \in DeleteKey:
        \/ JobDeleteKey(k)
        \/ JobInsertKey(k)
    \/ JobDeleteFinish
    \/ JobInsertFinish

    \/ Terminated

Spec == Init /\ [][Next]_vars

FairSpec == Spec /\ WF_vars(Next)

-------------------------------------------------------

AlwaysTerminate == []<>TerminateCond


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

WhenTerminatedJobInv ==
    TerminateCond =>
        /\ job_mem_keys = {}
        /\ job_disk_keys = {}
        /\ job_loading = FALSE
        /\ deleted_keys = {}


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


SoftDeleteInv ==
    \A n \in Node:
        LET
            old_addr == local_addr[n]
            new_addr == local_new_addr[n]

            old_key == global_state[old_addr].key
            new_key == global_state[new_addr].key

            pre_cond ==
                /\ ENABLED SoftDelete(n)

            cond ==
                /\ old_addr # new_addr
                /\ old_key # new_key
                /\ disk[old_key] # nil
                /\ disk[new_key] = nil
                /\ global_state[old_addr].status = "WriteLock"
                /\ global_state[new_addr].status = "WriteLock"
        IN
            pre_cond => cond


RecoverInv ==
    \A n \in Node:
        LET
            old_addr == local_addr[n]
            new_addr == local_new_addr[n]

            old_key == global_state[old_addr].key
            new_key == global_state[new_addr].key

            pre_cond ==
                /\ ENABLED Recover(n)

            cond ==
                /\ old_addr # new_addr
                /\ old_key # new_key
                /\ disk[old_key] # nil
                /\ disk[new_key] = nil
                /\ global_state[old_addr].status = "WriteLock"
                /\ global_state[new_addr].status = "WriteLock"
        IN
            pre_cond => cond

HardDeleteInv ==
    \A n \in Node:
        LET
            addr == local_addr[n]
            key == global_state[addr].key

            pre_cond ==
                /\ ENABLED HardDelete(n)

            cond ==
                /\ disk[key] # nil
                /\ global_state[addr].status = "WriteLock"
        IN
            pre_cond => cond


JobDeleteInv ==
    \/ ~(\E k \in DeleteKey: ENABLED JobDeleteKey(k))
    \/ ~(ENABLED JobDeleteFinish)

JobInsertInv ==
    \/ ~(\E k \in DeleteKey: ENABLED JobInsertKey(k))
    \/ ~(ENABLED JobInsertFinish)


ReverseCond ==
    \A n \in Node: ~(ENABLED HardDelete(n))

====

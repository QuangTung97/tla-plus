------ MODULE S3Slave ----
EXTENDS TLC, Naturals

CONSTANTS Node, nil, max_restart

VARIABLES pc,
    status, slave_locked, slave_generation, status_can_expire,
    next_value, slave_value, kept_value,
    slave_write_version,
    db_status, db_generation, db_write_version,
    local_version, local_generation,
    master_generation,
    enable_delete, num_restart

slave_vars == <<
    status, slave_generation, status_can_expire,
    next_value, slave_value, kept_value,
    slave_write_version
>>

db_vars == <<db_status, db_generation, db_write_version>>

vars == <<
    pc, local_version, local_generation, slave_locked,
    slave_vars, db_vars, master_generation, enable_delete,
    num_restart
>>

---------------------------------------------------------------

PC == {
    "Init",
    "FinishWrite", "SendWriteComplete",
    "S3Delete", "DeleteUnlock", "FinishDelete",
    "Terminated"
}

WritePC == {"FinishWrite", "SendWriteComplete"}

Status == {"Writing", "WriteComplete", "Deleted"}
NullStatus == Status \union {nil}

DBStatus == {"Empty", "Written", "Deleting", "Deleted"}

Generation == 0..10
NullGeneration == Generation \union {nil}

WriteValue == 20..29
NullWriteValue == WriteValue \union {nil}

WriteVersion == 30..39
NullWriteVersion == WriteVersion \union {nil}

---------------------------------------------------------------

TypeOK ==
    /\ pc \in [Node -> PC]
    /\ status \in NullStatus
    /\ slave_locked \in BOOLEAN
    /\ slave_generation \in Generation
    /\ status_can_expire \in BOOLEAN

    /\ next_value \in WriteValue
    /\ slave_value \in NullWriteValue
    /\ kept_value \in NullWriteValue

    /\ slave_write_version \in WriteVersion
    /\ db_write_version \in NullWriteVersion

    /\ master_generation \in Generation

    /\ db_status \in DBStatus
    /\ db_generation \in Generation
    /\ enable_delete \in BOOLEAN

    /\ local_version \in [Node -> NullWriteVersion]
    /\ local_generation \in [Node -> NullGeneration]

    /\ num_restart \in 0..max_restart

Init ==
    /\ pc = [n \in Node |-> "Init"]
    /\ status = nil
    /\ slave_locked = FALSE
    /\ status_can_expire = FALSE
    /\ slave_generation = 0

    /\ next_value = 20
    /\ slave_value = nil
    /\ kept_value = nil

    /\ slave_write_version = 30
    /\ db_write_version = nil

    /\ master_generation = 1

    /\ db_status = "Empty"
    /\ db_generation = 1
    /\ enable_delete = TRUE

    /\ local_version = [n \in Node |-> nil]
    /\ local_generation = [n \in Node |-> nil]

    /\ num_restart = 0

    /\ WritePC \subseteq PC

---------------------------------------------------------------

slaveUnchanged ==
    /\ UNCHANGED master_generation
    /\ UNCHANGED enable_delete
    /\ UNCHANGED <<local_version, local_generation>>
    /\ UNCHANGED num_restart

value_vars == <<next_value, slave_value, kept_value>>

goto(n, l) ==
    pc' = [pc EXCEPT ![n] = l]

writing_set == {n \in Node: pc[n] \in WritePC}

lockSlave ==
    /\ ~slave_locked
    /\ slave_locked' = TRUE

unlockSlave ==
    /\ slave_locked' = FALSE

Write(n) ==
    LET
        allow_write ==
            \/ status \in {nil, "Writing", "WriteComplete"}
            \/ slave_generation < master_generation
    IN
    /\ pc[n] = "Init"
    /\ writing_set = {}
    /\ allow_write
    /\ ~slave_locked

    /\ goto(n, "FinishWrite")
    /\ status' = "Writing"
    /\ status_can_expire' = TRUE
    /\ slave_generation' = master_generation

    /\ next_value' = next_value + 1
    /\ slave_value' = next_value'
    /\ IF enable_delete
        THEN UNCHANGED kept_value
        ELSE kept_value' = slave_value'

    /\ slave_write_version' = slave_write_version + 1

    /\ UNCHANGED db_vars
    /\ UNCHANGED slave_locked
    /\ slaveUnchanged


FinishWrite(n) ==
    /\ pc[n] = "FinishWrite"
    /\ goto(n, "SendWriteComplete")
    /\ status' = "WriteComplete"
    /\ status_can_expire' = FALSE

    /\ UNCHANGED slave_write_version
    /\ UNCHANGED value_vars
    /\ UNCHANGED slave_generation
    /\ UNCHANGED slave_locked
    /\ UNCHANGED db_vars
    /\ slaveUnchanged


SendWriteComplete(n) ==
    /\ pc[n] = "SendWriteComplete"
    /\ goto(n, "Terminated")
    /\ db_status' = "Written"
    /\ db_write_version' = slave_write_version

    /\ UNCHANGED slave_locked
    /\ UNCHANGED db_generation
    /\ UNCHANGED slave_vars
    /\ slaveUnchanged


RestartWriting(n) ==
    /\ pc[n] = "Terminated"
    /\ writing_set = {}
    /\ ~slave_locked

    /\ status = "Writing"
    /\ status_can_expire

    /\ goto(n, "FinishWrite")

    /\ UNCHANGED slave_locked
    /\ UNCHANGED slave_vars
    /\ UNCHANGED db_vars
    /\ slaveUnchanged

---------------------------------------------------------------

deleteUnchanged ==
    /\ UNCHANGED enable_delete
    /\ UNCHANGED master_generation
    /\ UNCHANGED num_restart

StartDelete(n) ==
    LET
        allow_delete_normal ==
            /\ pc[n] = "Init"
            /\ enable_delete
            /\ db_status = "Written"

        restart_delete ==
            /\ pc[n] \in {"Init", "Terminated"}
            /\ db_status = "Deleting"

        allow_delete ==
            \/ allow_delete_normal
            \/ restart_delete
    IN
    /\ allow_delete

    /\ goto(n, "S3Delete")
    /\ db_status' = "Deleting"

    /\ local_version' = [local_version EXCEPT ![n] = db_write_version]
    /\ local_generation' = [local_generation EXCEPT ![n] = db_generation]

    /\ UNCHANGED slave_locked
    /\ UNCHANGED db_generation
    /\ UNCHANGED db_write_version
    /\ UNCHANGED slave_vars
    /\ deleteUnchanged


S3Delete(n) ==
    LET
        allow_delete ==
            /\ local_version[n] = slave_write_version

        when_normal ==
            /\ lockSlave
            /\ goto(n, "DeleteUnlock")
            /\ status' = "Deleted"
            /\ slave_generation' = local_generation[n]
            /\ status_can_expire' = FALSE
            /\ slave_value' = nil

            /\ UNCHANGED kept_value
            /\ UNCHANGED next_value
            /\ UNCHANGED <<local_version, local_generation>>

        when_fail ==
            /\ goto(n, "Terminated")
            /\ local_version' = [local_version EXCEPT ![n] = nil]
            /\ local_generation' = [local_generation EXCEPT ![n] = nil]
            /\ UNCHANGED slave_locked
            /\ UNCHANGED slave_vars
    IN
    /\ pc[n] = "S3Delete"

    /\ IF allow_delete
        THEN when_normal
        ELSE when_fail

    /\ UNCHANGED slave_write_version
    /\ UNCHANGED db_vars
    /\ deleteUnchanged


DeleteUnlock(n) ==
    /\ pc[n] = "DeleteUnlock"
    /\ goto(n, "FinishDelete")
    /\ unlockSlave

    /\ UNCHANGED db_vars
    /\ UNCHANGED slave_vars
    /\ UNCHANGED <<local_version, local_generation>>
    /\ deleteUnchanged


FinishDelete(n) ==
    /\ pc[n] = "FinishDelete"
    /\ goto(n, "Terminated")
    /\ db_status' = "Deleted"
    /\ db_generation' = db_generation + 1

    /\ local_version' = [local_version EXCEPT ![n] = nil]
    /\ local_generation' = [local_generation EXCEPT ![n] = nil]

    /\ UNCHANGED slave_locked
    /\ UNCHANGED db_write_version
    /\ UNCHANGED slave_vars
    /\ deleteUnchanged

---------------------------------------------------------------

MasterSync ==
    /\ master_generation < db_generation
    /\ master_generation' = db_generation
    /\ UNCHANGED db_vars
    /\ UNCHANGED slave_vars
    /\ UNCHANGED slave_locked
    /\ UNCHANGED pc
    /\ UNCHANGED enable_delete
    /\ UNCHANGED <<local_version, local_generation>>
    /\ UNCHANGED num_restart


DisableDelete ==
    /\ enable_delete
    /\ enable_delete' = FALSE

    /\ UNCHANGED slave_locked
    /\ UNCHANGED master_generation
    /\ UNCHANGED db_vars
    /\ UNCHANGED slave_vars
    /\ UNCHANGED pc
    /\ UNCHANGED <<local_version, local_generation>>
    /\ UNCHANGED num_restart

---------------------------------------------------------------

Restart(n) ==
    /\ pc[n] \notin {"Init", "Terminated"}
    /\ num_restart < max_restart
    /\ num_restart' = num_restart + 1

    /\ local_version' = [local_version EXCEPT ![n] = nil]
    /\ local_generation' = [local_generation EXCEPT ![n] = nil]

    /\ IF pc[n] \in {"S3Delete", "DeleteUnlock", "FinishDelete"}
        THEN goto(n, "Init")
        ELSE goto(n, "Terminated")

    /\ IF pc[n] = "DeleteUnlock"
        THEN slave_locked' = FALSE
        ELSE UNCHANGED slave_locked

    /\ UNCHANGED master_generation
    /\ UNCHANGED enable_delete
    /\ UNCHANGED db_vars
    /\ UNCHANGED slave_vars

---------------------------------------------------------------

TerminateCond ==
    /\ \A n \in Node: pc[n] = "Terminated"
    /\ ~enable_delete
    /\ ~slave_locked
    /\ status \in {"WriteComplete", "Deleted"}
    /\ db_status \in {"Written", "Deleted"}

Terminated ==
    /\ TerminateCond
    /\ UNCHANGED vars


Next ==
    \/ \E n \in Node:
        \/ Write(n)
        \/ FinishWrite(n)
        \/ SendWriteComplete(n)
        \/ RestartWriting(n)

        \/ StartDelete(n)
        \/ S3Delete(n)
        \/ DeleteUnlock(n)
        \/ FinishDelete(n)

        \/ Restart(n)
    \/ MasterSync
    \/ DisableDelete
    \/ Terminated

Spec == Init /\ [][Next]_vars

FairSpec == Spec /\ WF_vars(Next)

---------------------------------------------------------------

AlwaysTerminated == []<> TerminateCond


NotAllowConcurrentDelete ==
    LET
        write_set == {n \in Node: pc[n] = "FinishWrite"}
        delete_set == {n \in Node: pc[n] = "DeleteUnlock"}

        cond ==
            /\ write_set # {}
            /\ delete_set # {}
    IN
        ~cond


KeptValueMustPersist ==
    kept_value # nil => slave_value = kept_value

====

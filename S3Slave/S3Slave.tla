------ MODULE S3Slave ----
EXTENDS TLC, Naturals

CONSTANTS Node, nil

VARIABLES pc,
    status, slave_locked, slave_generation, status_can_expire,
    next_value, slave_value, kept_value,
    slave_write_version,
    db_status, db_generation, db_write_version,
    delete_local_version,
    master_generation,
    enable_delete

slave_vars == <<
    status, slave_generation, status_can_expire,
    next_value, slave_value, kept_value,
    slave_write_version
>>

db_vars == <<db_status, db_generation, db_write_version>>

vars == <<
    pc, delete_local_version, slave_locked,
    slave_vars, db_vars, master_generation, enable_delete
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

    /\ delete_local_version \in [Node -> NullWriteVersion]

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

    /\ delete_local_version = [n \in Node |-> nil]

    /\ WritePC \subseteq PC

---------------------------------------------------------------

slaveUnchanged ==
    /\ UNCHANGED master_generation
    /\ UNCHANGED enable_delete
    /\ UNCHANGED delete_local_version

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

---------------------------------------------------------------

deleteUnchanged ==
    /\ UNCHANGED enable_delete
    /\ UNCHANGED master_generation

StartDelete(n) ==
    LET
        allow_delete ==
            \/ /\ enable_delete
               /\ db_status = "Written"
            \/ db_status = "Deleting"
    IN
    /\ pc[n] = "Init"
    /\ allow_delete

    /\ goto(n, "S3Delete")
    /\ db_status' = "Deleting"
    /\ delete_local_version' = [delete_local_version EXCEPT ![n] = db_write_version]

    /\ UNCHANGED slave_locked
    /\ UNCHANGED db_generation
    /\ UNCHANGED db_write_version
    /\ UNCHANGED slave_vars
    /\ deleteUnchanged


S3Delete(n) ==
    LET
        allow_delete ==
            /\ delete_local_version[n] = slave_write_version

        when_normal ==
            /\ lockSlave
            /\ goto(n, "DeleteUnlock")
            /\ status' = "Deleted"
            /\ slave_generation' = db_generation
            /\ status_can_expire' = FALSE
            /\ slave_value' = nil

            /\ UNCHANGED kept_value
            /\ UNCHANGED next_value

        when_fail ==
            /\ goto(n, "Init")
            /\ UNCHANGED slave_locked
            /\ UNCHANGED slave_vars
    IN
    /\ pc[n] = "S3Delete"

    /\ IF allow_delete
        THEN when_normal
        ELSE when_fail

    /\ UNCHANGED slave_write_version
    /\ UNCHANGED db_vars
    /\ UNCHANGED delete_local_version
    /\ deleteUnchanged


DeleteUnlock(n) ==
    /\ pc[n] = "DeleteUnlock"
    /\ goto(n, "FinishDelete")
    /\ unlockSlave

    /\ UNCHANGED db_vars
    /\ UNCHANGED slave_vars
    /\ UNCHANGED delete_local_version
    /\ deleteUnchanged


FinishDelete(n) ==
    /\ pc[n] = "FinishDelete"
    /\ goto(n, "Terminated")
    /\ db_status' = "Deleted"
    /\ db_generation' = db_generation + 1
    /\ delete_local_version' = [delete_local_version EXCEPT ![n] = nil]

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
    /\ UNCHANGED delete_local_version


DisableDelete ==
    /\ enable_delete
    /\ enable_delete' = FALSE

    /\ UNCHANGED slave_locked
    /\ UNCHANGED master_generation
    /\ UNCHANGED db_vars
    /\ UNCHANGED slave_vars
    /\ UNCHANGED pc
    /\ UNCHANGED delete_local_version

---------------------------------------------------------------

Restart(n) ==
    /\ pc[n] \notin {"Init", "Terminated"}
    /\ delete_local_version' = [delete_local_version EXCEPT ![n] = nil]

    /\ IF pc[n] \in {"S3Delete", "FinishDelete"}
        THEN goto(n, "Init")
        ELSE goto(n, "Terminated")

    /\ slave_locked' = FALSE

    /\ UNCHANGED master_generation
    /\ UNCHANGED enable_delete
    /\ UNCHANGED db_vars
    /\ UNCHANGED slave_vars

---------------------------------------------------------------

TerminateCond ==
    /\ \A n \in Node: pc[n] = "Terminated"
    /\ ~enable_delete
    /\ ~slave_locked

Terminated ==
    /\ TerminateCond
    /\ UNCHANGED vars


Next ==
    \/ \E n \in Node:
        \/ Write(n)
        \/ FinishWrite(n)
        \/ SendWriteComplete(n)

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

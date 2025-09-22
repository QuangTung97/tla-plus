------ MODULE S3Slave ----
EXTENDS TLC, Naturals

CONSTANTS Node, nil

VARIABLES pc,
    status, slave_generation, status_can_expire,
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
    pc, delete_local_version,
    slave_vars, db_vars, master_generation, enable_delete
>>

---------------------------------------------------------------

PC == {
    "Init", "FinishWrite", "SendWriteComplete",
    "S3Delete", "FinishDelete",
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

Write(n) ==
    LET
        allow_write ==
            \/ status \in {nil, "Writing", "WriteComplete"}
            \/ slave_generation < master_generation
    IN
    /\ pc[n] = "Init"
    /\ writing_set = {}
    /\ allow_write

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
    /\ slaveUnchanged


FinishWrite(n) ==
    /\ pc[n] = "FinishWrite"
    /\ goto(n, "SendWriteComplete")
    /\ status' = "WriteComplete"
    /\ status_can_expire' = FALSE

    /\ UNCHANGED slave_write_version
    /\ UNCHANGED value_vars
    /\ UNCHANGED slave_generation
    /\ UNCHANGED db_vars
    /\ slaveUnchanged


SendWriteComplete(n) ==
    /\ pc[n] = "SendWriteComplete"
    /\ goto(n, "Terminated")
    /\ db_status' = "Written"
    /\ db_write_version' = slave_write_version
    /\ UNCHANGED db_generation
    /\ UNCHANGED slave_vars
    /\ slaveUnchanged

---------------------------------------------------------------

deleteUnchanged ==
    /\ UNCHANGED enable_delete
    /\ UNCHANGED master_generation

StartDelete(n) ==
    /\ pc[n] = "Init"
    /\ enable_delete
    /\ goto(n, "S3Delete")
    /\ db_status = "Written"
    /\ db_status' = "Deleting"
    /\ delete_local_version' = [delete_local_version EXCEPT ![n] = db_write_version]
    /\ UNCHANGED db_generation
    /\ UNCHANGED db_write_version
    /\ UNCHANGED slave_vars
    /\ deleteUnchanged


S3Delete(n) ==
    LET
        allow_delete ==
            /\ delete_local_version[n] = slave_write_version

        when_normal ==
            /\ goto(n, "FinishDelete")
            /\ status' = "Deleted"
            /\ slave_generation' = db_generation
            /\ status_can_expire' = FALSE
            /\ slave_value' = nil

            /\ UNCHANGED kept_value
            /\ UNCHANGED next_value

        when_fail ==
            /\ goto(n, "Init")
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


FinishDelete(n) ==
    /\ pc[n] = "FinishDelete"
    /\ goto(n, "Terminated")
    /\ db_status' = "Deleted"
    /\ db_generation' = db_generation + 1
    /\ delete_local_version' = [delete_local_version EXCEPT ![n] = nil]
    /\ UNCHANGED db_write_version
    /\ UNCHANGED slave_vars
    /\ deleteUnchanged

---------------------------------------------------------------

MasterSync ==
    /\ master_generation < db_generation
    /\ master_generation' = db_generation
    /\ UNCHANGED db_vars
    /\ UNCHANGED slave_vars
    /\ UNCHANGED pc
    /\ UNCHANGED enable_delete
    /\ UNCHANGED delete_local_version


DisableDelete ==
    /\ enable_delete
    /\ enable_delete' = FALSE
    /\ UNCHANGED master_generation
    /\ UNCHANGED db_vars
    /\ UNCHANGED slave_vars
    /\ UNCHANGED pc
    /\ UNCHANGED delete_local_version

---------------------------------------------------------------

TerminateCond ==
    /\ \A n \in Node: pc[n] = "Terminated"
    /\ ~enable_delete

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
        \/ FinishDelete(n)
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
        delete_set == {n \in Node: pc[n] = "FinishDelete"}

        cond ==
            /\ write_set # {}
            /\ delete_set # {}
    IN
        ~cond


KeptValueMustPersist ==
    kept_value # nil => slave_value = kept_value

====

------ MODULE S3Slave ----
EXTENDS TLC

CONSTANTS Node, nil

VARIABLES pc, status, status_can_expire,
    db_status, enable_delete

slave_vars == <<status, status_can_expire>>

vars == <<pc, slave_vars, db_status, enable_delete>>

---------------------------------------------------------------

PC == {
    "Init", "FinishWrite", "SendWriteComplete",
    "SlaveDelete", "FinishDelete",
    "Terminated"
}

WritePC == {"FinishWrite", "SendWriteComplete"}

Status == {"Writing", "WriteComplete", "Deleted"}

NullStatus == Status \union {nil}

DBStatus == {"Empty", "Written", "Deleting", "Deleted"}

---------------------------------------------------------------

TypeOK ==
    /\ pc \in [Node -> PC]
    /\ status \in NullStatus
    /\ status_can_expire \in BOOLEAN
    /\ db_status \in DBStatus
    /\ enable_delete \in BOOLEAN

Init ==
    /\ pc = [n \in Node |-> "Init"]
    /\ status = nil
    /\ status_can_expire = FALSE
    /\ db_status = "Empty"
    /\ enable_delete = TRUE

    /\ WritePC \subseteq PC

---------------------------------------------------------------

goto(n, l) ==
    pc' = [pc EXCEPT ![n] = l]

writing_set == {n \in Node: pc[n] \in WritePC}

Write(n) ==
    LET
        allow_write ==
            \/ status \in {nil, "Writing", "WriteComplete"}

        when_normal ==
            /\ goto(n, "FinishWrite")
            /\ status' = "Writing"
            /\ status_can_expire' = TRUE

        when_fail ==
            /\ goto(n, "Init")
            /\ UNCHANGED slave_vars
    IN
    /\ pc[n] = "Init"
    /\ writing_set = {}
    /\ IF allow_write
        THEN when_normal
        ELSE when_fail

    /\ UNCHANGED db_status
    /\ UNCHANGED enable_delete


FinishWrite(n) ==
    /\ pc[n] = "FinishWrite"
    /\ goto(n, "SendWriteComplete")
    /\ status' = "WriteComplete"
    /\ status_can_expire' = FALSE
    /\ UNCHANGED db_status
    /\ UNCHANGED enable_delete


SendWriteComplete(n) ==
    /\ pc[n] = "SendWriteComplete"
    /\ goto(n, "Terminated")
    /\ db_status' = "Written"
    /\ UNCHANGED slave_vars
    /\ UNCHANGED enable_delete

---------------------------------------------------------------

StartDelete(n) ==
    /\ pc[n] = "Init"
    /\ enable_delete
    /\ goto(n, "SlaveDelete")
    /\ db_status = "Written"
    /\ db_status' = "Deleting"
    /\ UNCHANGED slave_vars
    /\ UNCHANGED enable_delete


S3Delete(n) ==
    LET
        when_normal ==
            /\ goto(n, "FinishDelete")
            /\ status' = "Deleted"
            /\ status_can_expire' = FALSE

        when_fail ==
            /\ goto(n, "Init")
            /\ UNCHANGED slave_vars
    IN
    /\ pc[n] = "SlaveDelete"
    /\ IF status = "WriteComplete"
        THEN when_normal
        ELSE when_fail

    /\ UNCHANGED db_status
    /\ UNCHANGED enable_delete


FinishDelete(n) ==
    /\ pc[n] = "FinishDelete"
    /\ goto(n, "Terminated")
    /\ db_status' = "Deleted"
    /\ UNCHANGED slave_vars
    /\ UNCHANGED enable_delete

---------------------------------------------------------------

TerminateCond ==
    /\ \A n \in Node: pc[n] = "Terminated"

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
    \/ Terminated

Spec == Init /\ [][Next]_vars

---------------------------------------------------------------

NotAllowConcurrentDelete ==
    LET
        write_set == {n \in Node: pc[n] = "FinishWrite"}
        delete_set == {n \in Node: pc[n] = "FinishDelete"}

        cond ==
            /\ write_set # {}
            /\ delete_set # {}
    IN
        ~cond

====

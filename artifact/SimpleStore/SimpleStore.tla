---- MODULE SimpleStore ----
EXTENDS TLC, Naturals, Sequences, FiniteSets

CONSTANTS Disk, Key, Digest, nil

VARIABLES
    global_isr,
    db, key_db,
    disk_db, files,
    stop_action

core_vars == <<global_isr, db, key_db>>

disk_vars == <<
    disk_db,
    files
>>

vars == <<
    core_vars,
    disk_vars,
    stop_action
>>

--------------------------------------------------------------------------

Null(S) ==  S \union {nil}

NonEmpty(S) == (SUBSET S) \ {{}}

--------------------------------------------------------------------------

Version == 1..9

DBState == [
    status: {"Writing", "Ready"},
    isr: NonEmpty(Disk),
    written: SUBSET Disk,
    version: Version
]

DiskState == [
    status: {"Active", "Deleted"},
    version: Version
]

--------------------------------------------------------------------------

TypeOK ==
    /\ global_isr \in NonEmpty(Disk)
    /\ db \in [Digest -> Null(DBState)]
    /\ key_db \in [Key -> Null(Digest)]

    /\ disk_db \in [Disk -> [Digest -> Null(DiskState)]]
    /\ files \in [Disk -> SUBSET Digest]

    /\ stop_action \in BOOLEAN

Init ==
    /\ global_isr \in NonEmpty(Disk)
    /\ db = [d \in Digest |-> nil]
    /\ key_db = [k \in Key |-> nil]

    /\ disk_db = [s \in Disk |-> [d \in Digest |-> nil]]
    /\ files = [s \in Disk |-> {}]

    /\ stop_action = FALSE

--------------------------------------------------------------------------

PutObject(k, d) ==
    LET
        db_state == [
            status |-> "Writing",
            isr |-> global_isr,
            written |-> {},
            version |-> 1
        ]
    IN
    /\ ~stop_action
    /\ key_db[k] # nil => key_db[k] # d
    /\ key_db' = [key_db EXCEPT ![k] = d]
    /\ db' = [db EXCEPT ![d] = db_state]

    /\ UNCHANGED global_isr
    /\ UNCHANGED disk_vars
    /\ UNCHANGED stop_action

--------------------------------------------------------------------------

WriteData(d, s) ==
    LET
        state == [
            status |-> "Active",
            version |-> db[d].version
        ]
    IN
    /\ db[d] # nil
    /\ db[d].status = "Writing"
    /\ d \notin files[s]

    /\ files' = [files EXCEPT ![s] = @ \union {d}]
    /\ disk_db' = [disk_db EXCEPT ![s][d] = state]

    /\ UNCHANGED core_vars
    /\ UNCHANGED stop_action

--------------------------------------------------------------------------

AckWrite(d, s) ==
    /\ db[d] # nil
    /\ db[d].status = "Writing"
    /\ d \in files[s]
    /\ s \notin db[d].written

    /\ db' = [db EXCEPT ![d].written = @ \union {s}]

    /\ UNCHANGED key_db
    /\ UNCHANGED global_isr
    /\ UNCHANGED disk_vars
    /\ UNCHANGED stop_action

--------------------------------------------------------------------------

StopMoreAction ==
    /\ ~stop_action
    /\ stop_action' = TRUE
    /\ UNCHANGED core_vars
    /\ UNCHANGED disk_vars

--------------------------------------------------------------------------

TerminateCond ==
    /\ stop_action
    /\ \A d \in Digest:
        db[d] # nil =>
            \/ db[d].status = "Ready"

Terminated ==
    /\ TerminateCond
    /\ UNCHANGED vars

--------------------------------------------------------------------------

Next ==
    \/ \E k \in Key, d \in Digest:
        \/ PutObject(k, d)
    \/ \E d \in Digest, s \in Disk:
        \/ WriteData(d, s)
        \/ AckWrite(d, s)
    \/ StopMoreAction
    \/ Terminated

Spec == Init /\ [][Next]_vars

--------------------------------------------------------------------------


====

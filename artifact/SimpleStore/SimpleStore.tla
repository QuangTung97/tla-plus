---- MODULE SimpleStore ----
EXTENDS TLC, Naturals, Sequences, FiniteSets

CONSTANTS Disk, Key, Digest, max_action, nil

VARIABLES
    global_isr,
    db, key_db,
    disk_db, files,
    msgs,
    num_action

core_vars == <<global_isr, db, key_db>>

disk_vars == <<
    disk_db,
    files
>>

vars == <<
    core_vars,
    disk_vars,
    msgs,
    num_action
>>

--------------------------------------------------------------------------

Null(S) ==  S \union {nil}

NonEmpty(S) == (SUBSET S) \ {{}}

--------------------------------------------------------------------------

Version == 1..9

DBState == [
    refcount: Nat,
    isr: NonEmpty(Disk),
    written: SUBSET Disk,
    writing: SUBSET Disk,
    deleting: SUBSET Disk,
    version: Version
]

DiskState == [
    status: {"Active", "Deleted"},
    version: Version
]

Msg ==
    LET
        put_req == [
            type: {"Put"},
            disk: Disk,
            digest: Digest,
            version: Version
        ]
    IN
    UNION {put_req}

--------------------------------------------------------------------------

TypeOK ==
    /\ global_isr \in NonEmpty(Disk)
    /\ db \in [Digest -> Null(DBState)]
    /\ key_db \in [Key -> Null(Digest)]

    /\ disk_db \in [Disk -> [Digest -> Null(DiskState)]]
    /\ files \in [Disk -> SUBSET Digest]

    /\ msgs \subseteq Msg

    /\ num_action \in 0..max_action

Init ==
    /\ global_isr \in NonEmpty(Disk)
    /\ db = [d \in Digest |-> nil]
    /\ key_db = [k \in Key |-> nil]

    /\ disk_db = [s \in Disk |-> [d \in Digest |-> nil]]
    /\ files = [s \in Disk |-> {}]

    /\ msgs = {}

    /\ num_action = 0

--------------------------------------------------------------------------

inc_action ==
    /\ num_action < max_action
    /\ num_action' = num_action + 1

--------------------------------------------------------------------------

PutObject(k, d) ==
    LET
        db_state == [
            refcount |-> 1,
            isr |-> global_isr,
            written |-> {},
            writing |-> global_isr,
            deleting |-> {},
            version |-> 1
        ]

        put_req(s) == [
            type |-> "Put",
            disk |-> s,
            digest |-> d,
            version |-> 1
        ]

        put_req_list == {put_req(s): s \in global_isr}

        when_new ==
            /\ db' = [db EXCEPT ![d] = db_state]

        when_exist ==
            /\ db' = [db EXCEPT ![d].refcount = @ + 1]
    IN
    /\ inc_action
    /\ key_db[k] # nil => key_db[k] # d
    /\ key_db' = [key_db EXCEPT ![k] = d]
    /\ IF db[d] = nil
        THEN when_new
        ELSE when_exist

    /\ msgs' = msgs \union put_req_list

    /\ UNCHANGED global_isr
    /\ UNCHANGED disk_vars

--------------------------------------------------------------------------

DeleteObject(k) ==
    /\ FALSE \* TODO
    /\ inc_action
    /\ key_db[k] # nil

    /\ UNCHANGED global_isr
    /\ UNCHANGED disk_vars

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
    /\ s \in db[d].isr
    /\ d \notin files[s]

    /\ files' = [files EXCEPT ![s] = @ \union {d}]
    /\ disk_db' = [disk_db EXCEPT ![s][d] = state]

    /\ UNCHANGED core_vars
    /\ UNCHANGED num_action

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
    /\ UNCHANGED num_action

--------------------------------------------------------------------------

TerminateCond ==
    /\ num_action = max_action
    /\ \A d \in Digest:
        db[d] # nil => db[d].isr = db[d].written

Terminated ==
    /\ TerminateCond
    /\ UNCHANGED vars

--------------------------------------------------------------------------

Next ==
    \/ \E k \in Key, d \in Digest:
        \/ PutObject(k, d)
    \/ \E k \in Key:
        \/ DeleteObject(k)
    \/ \E d \in Digest, s \in Disk:
        \/ WriteData(d, s)
        \/ AckWrite(d, s)
    \/ Terminated

Spec == Init /\ [][Next]_vars

--------------------------------------------------------------------------

DiskDBMatchFiles ==
    \A s \in Disk, d \in Digest:
        LET
            digest_exist ==
                /\ disk_db[s][d] # nil
                /\ disk_db[s][d].status = "Active"
        IN
        d \in files[s] <=> digest_exist

-------------------------

\* TODO can not delete while refcount > 1

--------------------------------------------------------------------------

====

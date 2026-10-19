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

Version == 1..max_action

ReqMap == [Disk -> Null(Version)]

init_req_map == [d \in Disk |-> nil]

DBState == [
    refcount: Nat,
    isr: SUBSET Disk,
    written: SUBSET Disk,
    writing: ReqMap,
    deleting: ReqMap,
    version: Version
]

DiskState == [
    status: {"Active", "Deleted"},
    version: Version
]

Msg ==
    LET
        put_req == [
            type: {"PutReq"},
            disk: Disk,
            digest: Digest,
            version: Version
        ]

        put_resp == [
            type: {"PutResp"},
            disk: Disk,
            digest: Digest,
            version: Version
        ]
    IN
    UNION {put_req, put_resp}

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

-------------------------

get_isr(d) ==
    IF db[d] = nil
        THEN {}
        ELSE db[d].isr

-------------------------

get_refcount(d) ==
    IF db[d] = nil
        THEN 0
        ELSE db[d].refcount

-------------------------

dec_ref_and_delete(d, input_db) ==
    IF input_db[d].refcount = 1 THEN
        [input_db EXCEPT
            ![d].refcount = @ - 1,
            ![d].isr = {},
            ![d].version = @ + 1
        ]
    ELSE
        [input_db EXCEPT ![d].refcount = @ - 1]

-------------------------

set_req_map(input_map, digest_set, version) ==
    LET
        do_update(d, old) ==
            IF d \in digest_set
                THEN version
                ELSE old
    IN
    [d \in Disk |-> do_update(d, input_map[d])]

--------------------------------------------------------------------------

PutObject(k, d) ==
    LET
        db_state == [
            refcount |-> 1,
            isr |-> global_isr,
            written |-> {},
            writing |-> set_req_map(init_req_map, global_isr, 1),
            deleting |-> init_req_map,
            version |-> 1
        ]

        put_req(s) == [
            type |-> "PutReq",
            disk |-> s,
            digest |-> d,
            version |-> 1
        ]

        old_digest == key_db[k]

        db_deleted ==
            IF old_digest # nil THEN
                dec_ref_and_delete(old_digest, db)
            ELSE
                db

        put_req_list == {put_req(s): s \in global_isr}

        when_new ==
            /\ db' = [db_deleted EXCEPT ![d] = db_state]

        when_exist ==
            /\ db' = [db_deleted EXCEPT ![d].refcount = @ + 1]
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
    LET
        d == key_db[k]
    IN
    /\ inc_action
    /\ key_db[k] # nil

    /\ key_db' = [key_db EXCEPT ![k] = nil]
    /\ db' = dec_ref_and_delete(d, db)
    /\ UNCHANGED msgs \* TODO

    /\ UNCHANGED global_isr
    /\ UNCHANGED disk_vars

--------------------------------------------------------------------------

doWriteData(req) ==
    LET
        s == req.disk
        d == req.digest

        state == [
            status |-> "Active",
            version |-> req.version
        ]

        put_resp == [
            type |-> "PutResp",
            disk |-> s,
            digest |-> d,
            version |-> req.version
        ]
    IN
    /\ d \notin files[s]

    /\ files' = [files EXCEPT ![s] = @ \union {d}]
    /\ disk_db' = [disk_db EXCEPT ![s][d] = state]
    /\ msgs' = msgs \union {put_resp}

    /\ UNCHANGED core_vars
    /\ UNCHANGED num_action

WriteData ==
    \E req \in msgs:
        /\ req.type = "PutReq"
        /\ doWriteData(req)

--------------------------------------------------------------------------

doAckWrite(resp) ==
    LET
        d == resp.digest
        s == resp.disk
    IN
    /\ db[d].writing[s] = resp.version

    /\ db' = [db EXCEPT
            ![d].writing = set_req_map(@, {s}, nil),
            ![d].written = @ \union {s}
        ]

    /\ UNCHANGED msgs
    /\ UNCHANGED key_db
    /\ UNCHANGED global_isr
    /\ UNCHANGED disk_vars
    /\ UNCHANGED num_action

AckWrite ==
    \E resp \in msgs:
        /\ resp.type = "PutResp"
        /\ doAckWrite(resp)

--------------------------------------------------------------------------

StopWriteCond ==
    /\ ~(ENABLED WriteData)
    /\ ~(ENABLED AckWrite)

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
    \/ WriteData
    \/ AckWrite
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

KeyDBMatchRefCount ==
    LET
        keys_by_digest(d) == {k \in Key: key_db[k] = d}

        num_keys(d) == Cardinality(keys_by_digest(d))
    IN
        \A d \in Digest: num_keys(d) = get_refcount(d)

-------------------------

WhenStopWriteInv ==
    LET

        digest_inv(d) ==
            \A s \in Disk: s \in get_isr(d) <=> d \in files[s]
    IN
    StopWriteCond =>
        /\ \A d \in Digest: digest_inv(d)

-------------------------

DigestIsrInv ==
    \A d \in Digest:
        get_refcount(d) = 0 <=> get_isr(d) = {}

-------------------------

\* TODO handle deleting & writing req map

--------------------------------------------------------------------------

====

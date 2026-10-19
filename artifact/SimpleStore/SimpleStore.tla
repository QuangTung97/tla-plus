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

        delete_req == [
            type: {"DeleteReq"},
            disk: Disk,
            digest: Digest,
            version: Version
        ]

        delete_resp == [
            type: {"DeleteResp"},
            disk: Disk,
            digest: Digest,
            version: Version
        ]
    IN
    UNION {put_req, put_resp, delete_req, delete_resp}

--------------------------------------------------------------------------

TypeOK ==
    /\ global_isr \in NonEmpty(Disk)
    /\ db \in [Digest -> Null(DBState)]
    /\ key_db \in [Key -> Null(Digest)]

    /\ disk_db \in [Disk -> [Digest -> Null(Version)]]
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

deleting_from_writing(req_map, new_version) ==
    LET
        do_update(old) ==
            IF old # nil
                THEN new_version
                ELSE old
    IN
    [s \in Disk |-> do_update(req_map[s])]

-------------------------

dec_ref_and_delete(d, input_db) ==
    LET
        new_version == input_db[d].version + 1
        old_writing == input_db[d].writing
        new_deleting == deleting_from_writing(old_writing, new_version)
    IN
    IF input_db[d].refcount = 1 THEN
        [input_db EXCEPT
            ![d].refcount = @ - 1,
            ![d].isr = {},
            ![d].writing = init_req_map,
            ![d].deleting = new_deleting,
            ![d].version = new_version
        ]
    ELSE
        [input_db EXCEPT ![d].refcount = @ - 1]

-------------------------

build_put_requests(d, input_db, disks) ==
    LET
        put_req(s) == [
            type |-> "PutReq",
            disk |-> s,
            digest |-> d,
            version |-> input_db[d].version
        ]
    IN
    {put_req(s): s \in disks}

-------------------------

build_delete_requests(d, input_db, disks) ==
    LET
        delete_req(s) == [
            type |-> "DeleteReq",
            disk |-> s,
            digest |-> d,
            version |-> input_db[d].version
        ]
    IN
    {delete_req(s): s \in disks}

-------------------------

get_req_disks(req_map) ==
    {s \in Disk: req_map[s] # nil}

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

        old_digest == key_db[k]

        db_deleted ==
            IF old_digest # nil THEN
                dec_ref_and_delete(old_digest, db)
            ELSE
                db

        when_new ==
            /\ db' = [db_deleted EXCEPT ![d] = db_state]

        when_exist ==
            /\ db' = [db_deleted EXCEPT ![d].refcount = @ + 1]

        put_reqs == build_put_requests(d, db', global_isr)

        delete_reqs == build_delete_requests(
            d, db',
            get_req_disks(db'[d].deleting)
        )
    IN
    /\ inc_action
    /\ key_db[k] # nil => key_db[k] # d

    /\ key_db' = [key_db EXCEPT ![k] = d]
    /\ IF db[d] = nil
        THEN when_new
        ELSE when_exist
    /\ msgs' = msgs \union put_reqs \union delete_reqs

    /\ UNCHANGED global_isr
    /\ UNCHANGED disk_vars

--------------------------------------------------------------------------

DeleteObject(k) ==
    LET
        d == key_db[k]

        delete_reqs == build_delete_requests(
            d, db',
            get_req_disks(db'[d].deleting)
        )
    IN
    /\ inc_action
    /\ key_db[k] # nil

    /\ key_db' = [key_db EXCEPT ![k] = nil]
    /\ db' = dec_ref_and_delete(d, db)
    /\ msgs' = msgs \union delete_reqs

    /\ UNCHANGED global_isr
    /\ UNCHANGED disk_vars

--------------------------------------------------------------------------

get_disk_version(s, d) ==
    IF disk_db[s][d] = nil
        THEN 0
        ELSE disk_db[s][d]

--------------------------------------------------------------------------

doWriteData(req) ==
    LET
        s == req.disk
        d == req.digest

        put_resp == [
            type |-> "PutResp",
            disk |-> s,
            digest |-> d,
            version |-> req.version
        ]
    IN
    /\ req.version > get_disk_version(s, d)

    /\ files' = [files EXCEPT ![s] = @ \union {d}]
    /\ disk_db' = [disk_db EXCEPT ![s][d] = req.version]
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

doDeleteData(req) ==
    LET
        d == req.digest
        s == req.disk

        delete_resp == [
            type |-> "DeleteResp",
            disk |-> s,
            digest |-> d,
            version |-> req.version
        ]
    IN
    /\ req.version > get_disk_version(s, d)

    /\ disk_db' = [disk_db EXCEPT ![s][d] = req.version]
    /\ files' = [files EXCEPT ![s] = @ \ {d}]
    /\ msgs' = msgs \union {delete_resp}

    /\ UNCHANGED core_vars
    /\ UNCHANGED num_action

DeleteData ==
    \E req \in msgs:
        /\ req.type = "DeleteReq"
        /\ doDeleteData(req)

--------------------------------------------------------------------------

StopWriteCond ==
    /\ ~(ENABLED WriteData)
    /\ ~(ENABLED DeleteData)
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
    \/ DeleteData
    \/ Terminated

Spec == Init /\ [][Next]_vars

--------------------------------------------------------------------------

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

EveryWritingIsInIsr ==
    LET
        cond(d) ==
            \A s \in Disk: db[d].writing[s] # nil => s \in db[d].isr
    IN
    \A d \in Digest:
        db[d] # nil => cond(d)

-------------------------

EveryDeletingIsNotInIsr ==
    LET
        cond(d) ==
            \A s \in Disk: db[d].deleting[s] # nil => s \notin db[d].isr
    IN
    \A d \in Digest:
        db[d] # nil => cond(d)

--------------------------------------------------------------------------

====

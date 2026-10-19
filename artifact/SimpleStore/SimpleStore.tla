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

deleting_from_writing(old_written, old_writing, new_version) ==
    LET
        do_delete(s, old) ==
            IF s \in old_written \/ old # nil
                THEN new_version
                ELSE old
    IN
    [s \in Disk |-> do_delete(s, old_writing[s])]

-------------------------

get_req_disks(req_map) ==
    {s \in Disk: req_map[s] # nil}

-------------------------

set_req_map(input_map, set_disks, clear_disks, new_value) ==
    LET
        do_update(s, old) ==
            IF s \in set_disks THEN
                new_value
            ELSE IF s \in clear_disks THEN
                nil
            ELSE
                old
    IN
    [s \in Disk |-> do_update(s, input_map[s])]

-------------------------

build_put_requests(d, disks, new_version) ==
    LET
        put_req(s) == [
            type |-> "PutReq",
            disk |-> s,
            digest |-> d,
            version |-> new_version
        ]
    IN
    {put_req(s): s \in disks}

-------------------------

build_delete_requests(d, disks, new_version) ==
    LET
        delete_req(s) == [
            type |-> "DeleteReq",
            disk |-> s,
            digest |-> d,
            version |-> new_version
        ]
    IN
    {delete_req(s): s \in disks}

-------------------------

build_action_info(d, input_db, new_isr, new_version) ==
    LET
        writing_set == get_req_disks(input_db.writing)
        deleting_set == get_req_disks(input_db.deleting)

        existed_set == input_db.written \union writing_set

        new_write_set == new_isr \ existed_set
        clear_write_set == writing_set \ new_isr

        extra_set == existed_set \ new_isr
        new_delete_set == extra_set \ deleting_set
        clear_delete_set == deleting_set \ extra_set

        put_reqs == build_put_requests(
            d, new_write_set, new_version
        )

        delete_reqs == build_delete_requests(
            d, new_delete_set, new_version
        )
    IN
    [
        written |-> (input_db.written \ new_write_set) \ new_delete_set,
        writing |-> set_req_map(
            input_db.writing, new_write_set, clear_write_set, new_version
        ),
        deleting |-> set_req_map(
            input_db.deleting, new_delete_set, clear_delete_set, new_version
        ),
        msgs |-> put_reqs \union delete_reqs
    ]

--------------------------------------------------------------------------

doPutObject(d, input_db) ==
    LET
        old_state ==
            IF input_db = nil THEN
                [
                    refcount |-> 0,
                    isr |-> {},
                    written |-> {},
                    writing |-> init_req_map,
                    deleting |-> init_req_map,
                    version |-> 0
                ]
            ELSE
                input_db

        new_version == old_state.version + 1

        actions == build_action_info(d, old_state, global_isr, new_version)

        new_state == [old_state EXCEPT
            !.refcount = 1,
            !.isr = global_isr,
            !.written = actions.written,
            !.writing = actions.writing,
            !.deleting = actions.deleting,
            !.version = new_version
        ]
    IN
        IF old_state.refcount = 0 THEN
            [
                db |-> new_state,
                msgs |-> actions.msgs
            ]
        ELSE
            [
                db |-> [old_state EXCEPT !.refcount = @ + 1],
                msgs |-> {}
            ]

--------------------------------------------------------------------------

doDeleteObject(d) ==
    LET
        old_state == db[d]
        new_version == old_state.version + 1

        actions == build_action_info(d, old_state, {}, new_version)

        new_state == [old_state EXCEPT
            !.refcount = 0,
            !.isr = {},
            !.written = actions.written,
            !.writing = actions.writing,
            !.deleting = actions.deleting,
            !.version = new_version
        ]
    IN
        IF old_state.refcount = 1 THEN
            [
                db |-> new_state,
                msgs |-> actions.msgs
            ]
        ELSE
            [
                db |-> [old_state EXCEPT !.refcount = @ - 1],
                msgs |-> {}
            ]

--------------------------------------------------------------------------

PutObject(k, d) ==
    LET
        old_digest == key_db[k]

        delete_actions == doDeleteObject(old_digest)

        db_deleted ==
            IF old_digest # nil THEN
                [db EXCEPT ![old_digest] = delete_actions.db]
            ELSE
                db

        delete_reqs ==
            IF old_digest # nil
                THEN delete_actions.msgs
                ELSE {}

        put_actions == doPutObject(d, db_deleted[d])
    IN
    /\ inc_action
    /\ key_db[k] # nil => key_db[k] # d

    /\ key_db' = [key_db EXCEPT ![k] = d]
    /\ db' = [db_deleted EXCEPT ![d] = put_actions.db]
    /\ msgs' = msgs \union delete_reqs \union put_actions.msgs

    /\ UNCHANGED global_isr
    /\ UNCHANGED disk_vars

--------------------------------------------------------------------------

DeleteObject(k) ==
    LET
        d == key_db[k]
        actions == doDeleteObject(d)
    IN
    /\ inc_action
    /\ key_db[k] # nil

    /\ key_db' = [key_db EXCEPT ![k] = nil]
    /\ db' = [db EXCEPT ![d] = actions.db]
    /\ msgs' = msgs \union actions.msgs

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
            ![d].writing = set_req_map(@, {s}, {}, nil),
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

doAckDelete(resp) ==
    LET
        d == resp.digest
        s == resp.disk
    IN
    /\ db[d].deleting[s] = resp.version

    /\ db' = [db EXCEPT
            ![d].deleting[s] = nil,
            ![d].written = @ \ {s}
        ]

    /\ UNCHANGED msgs
    /\ UNCHANGED key_db
    /\ UNCHANGED global_isr
    /\ UNCHANGED disk_vars
    /\ UNCHANGED num_action

AckDelete ==
    \E resp \in msgs:
        /\ resp.type = "DeleteResp"
        /\ doAckDelete(resp)

--------------------------------------------------------------------------

UpdateGlobalIsr ==
    /\ inc_action

    /\ global_isr' \in NonEmpty(Disk)
    /\ global_isr' # global_isr

    /\ UNCHANGED msgs
    /\ UNCHANGED db
    /\ UNCHANGED key_db
    /\ UNCHANGED disk_vars

--------------------------------------------------------------------------

SyncGlobalIsr(d) ==
    LET
        new_version == db[d].version + 1

        actions == build_action_info(d, db[d], global_isr, new_version)
    IN
    /\ get_isr(d) # {}
    /\ get_isr(d) # global_isr

    /\ db' = [db EXCEPT
            ![d].isr = global_isr,
            ![d].written = actions.written,
            ![d].writing = actions.writing,
            ![d].deleting = actions.deleting,
            ![d].version = new_version
        ]
    /\ msgs' = msgs \union actions.msgs

    /\ UNCHANGED num_action
    /\ UNCHANGED global_isr
    /\ UNCHANGED key_db
    /\ UNCHANGED disk_vars

--------------------------------------------------------------------------

StopWriteCond ==
    /\ ~(ENABLED WriteData)
    /\ ~(ENABLED DeleteData)
    /\ ~(ENABLED AckWrite)
    /\ ~(ENABLED AckDelete)

TerminateCond ==
    /\ num_action = max_action
    /\ StopWriteCond
    /\ \A d \in Digest:
        db[d] # nil =>
            /\ db[d].isr = db[d].written
            /\ db[d].isr # {} => db[d].isr = global_isr

Terminated ==
    /\ TerminateCond
    /\ UNCHANGED vars

--------------------------------------------------------------------------

Next ==
    \/ \E k \in Key, d \in Digest:
        \/ PutObject(k, d)
    \/ \E k \in Key:
        \/ DeleteObject(k)
    \/ \E d \in Digest:
        \/ SyncGlobalIsr(d)
    \/ WriteData
    \/ AckWrite
    \/ DeleteData
    \/ AckDelete
    \/ UpdateGlobalIsr
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

-------------------------

WrittenNotContainWritingOrDeleting ==
    LET
        cond(d) ==
            \A s \in Disk:
                s \in db[d].written =>
                    /\ db[d].writing[s] = nil
                    /\ db[d].deleting[s] = nil
    IN
    \A d \in Digest:
        db[d] # nil => cond(d)

-------------------------

NotBothWritingAndDeleting ==
    LET
        cond(d) ==
            \A s \in Disk:
                \/ db[d].deleting[s] = nil
                \/ db[d].writing[s] = nil
    IN
    \A d \in Digest:
        db[d] # nil => cond(d)

-------------------------

TerminateCondImplyStopCond ==
    TerminateCond => StopWriteCond

--------------------------------------------------------------------------

====

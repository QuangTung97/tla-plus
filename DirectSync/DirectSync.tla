------ MODULE DirectSync ----
EXTENDS TLC, Naturals, Sequences

CONSTANTS nil, max_val, max_sync_restart

VARIABLES
    local_disk, nfs_disk,
    local_mem_val, local_db_val, local_db_req, local_pc,
    current_req,
    job_map,
    db,
    num_sync_restart

vars == <<
    local_disk, nfs_disk,
    local_mem_val, local_db_val, local_db_req, local_pc,
    current_req,
    job_map,
    db,
    num_sync_restart
>>

disk_vars == <<local_disk, nfs_disk>>

local_vars == <<
    local_disk, local_mem_val,
    local_db_val, local_db_req,
    local_pc, current_req
>>

sync_vars == <<job_map>>

core_vars == <<db>>

----------------------------------------------------------------

Value == 20..max_val

NullValue == (Value \ {20}) \union {nil}

RequestID == 30..34

NullReq == RequestID \union {nil}

Job == [
    id: RequestID,
    status: {"Pending", "Syncing", "Finished"},
    val: NullValue
]

NullJob == Job \union {nil}

CoreDB == [
    val: Value,
    direct_id: NullReq,
    need_sync: BOOLEAN
]

----------------------------------------------------------------

TypeOK ==
    /\ local_disk \in Value
    /\ nfs_disk \in Value
    /\ local_mem_val \in NullValue
    /\ local_db_val \in Value
    /\ local_db_req \in NullReq
    /\ local_pc \in {"Init", "SendSync", "UpdateLocalDB"}
    /\ current_req \in RequestID

    /\ job_map \in [RequestID -> NullJob]
    /\ db \in CoreDB

    /\ num_sync_restart \in 0..max_sync_restart


Init ==
    /\ local_disk = 20
    /\ nfs_disk = 20
    /\ local_mem_val = nil
    /\ local_db_val = 20
    /\ local_db_req = nil
    /\ local_pc = "Init"
    /\ current_req = 30

    /\ job_map = [id \in RequestID |-> nil]
    /\ db = [val |-> 20, direct_id |-> nil, need_sync |-> FALSE]

    /\ num_sync_restart = 0

----------------------------------------------------------------

local_unchanged ==
    /\ UNCHANGED core_vars
    /\ UNCHANGED num_sync_restart

UpdateLocalDisk ==
    /\ local_disk < max_val
    /\ local_disk' = local_disk + 1
    /\ UNCHANGED local_pc
    /\ UNCHANGED local_mem_val
    /\ UNCHANGED local_db_val
    /\ UNCHANGED local_db_req
    /\ UNCHANGED nfs_disk
    /\ UNCHANGED current_req
    /\ local_unchanged
    /\ UNCHANGED sync_vars


ScanDiskChanged ==
    /\ local_pc = "Init"
    /\ local_disk # local_db_val
    /\ local_pc' = "SendSync"
    /\ current_req' = current_req + 1
    /\ local_mem_val' = local_disk
    /\ UNCHANGED disk_vars
    /\ UNCHANGED local_db_val
    /\ UNCHANGED local_db_req
    /\ UNCHANGED sync_vars
    /\ local_unchanged


SendSync ==
    LET
        init_job == [
            id |-> current_req,
            status |-> "Pending",
            val |-> nil
        ]
    IN
    /\ local_pc = "SendSync"
    /\ local_pc' = "UpdateLocalDB"
    /\ job_map' = [job_map EXCEPT ![current_req] = init_job]
    /\ UNCHANGED current_req
    /\ UNCHANGED disk_vars
    /\ UNCHANGED local_mem_val
    /\ UNCHANGED local_db_val
    /\ UNCHANGED local_db_req
    /\ local_unchanged


UpdateLocalDB ==
    /\ local_pc = "UpdateLocalDB"
    /\ local_pc' = "Init"
    /\ local_db_val' = local_mem_val
    /\ local_db_req' = current_req
    /\ local_mem_val' = nil
    /\ UNCHANGED current_req
    /\ UNCHANGED sync_vars
    /\ UNCHANGED disk_vars
    /\ local_unchanged


SendCoreSync ==
    LET
        when_match ==
            /\ db' = [db EXCEPT !.direct_id = nil]

        when_not_match ==
            /\ db' = [db EXCEPT !.need_sync = TRUE, !.direct_id = nil]
    IN
    /\ local_db_req # nil
    /\ local_db_req' = nil
    /\ IF local_db_req = db.direct_id
        THEN when_match
        ELSE when_not_match

    /\ UNCHANGED local_db_val
    /\ UNCHANGED local_mem_val
    /\ UNCHANGED local_pc

    /\ UNCHANGED current_req
    /\ UNCHANGED sync_vars
    /\ UNCHANGED disk_vars
    /\ UNCHANGED num_sync_restart

----------------------------------------------------------------

sync_unchanged ==
    /\ UNCHANGED core_vars
    /\ UNCHANGED local_vars
    /\ UNCHANGED num_sync_restart


StartSync(id) ==
    /\ job_map[id] # nil
    /\ job_map[id].status = "Pending"
    /\ job_map' = [job_map EXCEPT
            ![id].status = "Syncing"
        ]
    /\ UNCHANGED nfs_disk
    /\ sync_unchanged



FinishSync(id) ==
    /\ job_map[id] # nil
    /\ job_map[id].status = "Syncing"
    /\ nfs_disk' = local_disk
    /\ job_map' = [job_map EXCEPT
            ![id].status = "Finished",
            ![id].val = local_disk
        ]
    /\ sync_unchanged

----------------------------------------------------------------

GetDirectJob(id) ==
    LET
        update_direct_id ==
            IF db.need_sync
                THEN db
                ELSE [db EXCEPT !.direct_id = id]

        update_val ==
            IF db.val < job_map[id].val
                THEN [update_direct_id EXCEPT !.val = job_map[id].val]
                ELSE update_direct_id
    IN
    /\ job_map[id] # nil
    /\ job_map[id].status = "Finished"
    /\ job_map' = [job_map EXCEPT ![id] = nil]
    /\ db' = update_val
    /\ UNCHANGED nfs_disk
    /\ UNCHANGED local_vars
    /\ UNCHANGED num_sync_restart


CoreDoSync ==
    /\ db.need_sync
    /\ db' = [db EXCEPT
            !.need_sync = FALSE,
            !.val = local_disk
        ]
    /\ nfs_disk' = local_disk
    /\ UNCHANGED local_vars
    /\ UNCHANGED sync_vars
    /\ UNCHANGED num_sync_restart

----------------------------------------------------------------

RestartSync ==
    /\ num_sync_restart < max_sync_restart
    /\ num_sync_restart' = num_sync_restart + 1
    /\ job_map' = [id \in RequestID |-> nil]
    /\ UNCHANGED nfs_disk
    /\ UNCHANGED core_vars
    /\ UNCHANGED local_vars

----------------------------------------------------------------

StopCond ==
    /\ local_pc = "Init"
    /\ local_db_val = local_disk
    /\ \A id \in RequestID: job_map[id] = nil
    /\ local_db_req = nil
    /\ db.need_sync = FALSE

TerminateCond ==
    /\ StopCond
    /\ local_disk = max_val

Terminated ==
    /\ TerminateCond
    /\ UNCHANGED vars


Next ==
    \/ ScanDiskChanged
    \/ UpdateLocalDisk
    \/ SendSync
    \/ UpdateLocalDB
    \/ \E id \in RequestID:
        \/ StartSync(id)
        \/ FinishSync(id)
        \/ GetDirectJob(id)
    \/ RestartSync
    \/ SendCoreSync
    \/ CoreDoSync
    \/ Terminated

Spec == Init /\ [][Next]_vars

----------------------------------------------------------------

DataMatchInv ==
    StopCond =>
        /\ local_disk = nfs_disk
        /\ local_disk = local_db_val
        /\ local_disk = db.val


DirectIDInv ==
    db.need_sync => db.direct_id = nil

====

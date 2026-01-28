------ MODULE DirectSync ----
EXTENDS TLC, Naturals, Sequences

CONSTANTS nil, max_val, max_sync_restart

VARIABLES
    local_disk, nfs_disk,
    local_mem_val, local_db_val, local_pc,
    current_req,
    job_map,
    db,
    num_sync_restart

vars == <<
    local_disk, nfs_disk,
    local_mem_val, local_db_val, local_pc,
    current_req,
    job_map,
    db,
    num_sync_restart
>>

disk_vars == <<local_disk, nfs_disk>>

local_vars == <<local_disk, local_mem_val, local_db_val, local_pc, current_req>>

sync_vars == <<job_map>>

core_vars == <<db>>

----------------------------------------------------------------

Value == 20..max_val

NullValue == (Value \ {20}) \union {nil}

RequestID == 30..34

Job == [
    id: RequestID,
    status: {"Pending", "Syncing", "Finished"},
    val: NullValue
]

NullJob == Job \union {nil}

CoreDB == [
    val: Value
]

----------------------------------------------------------------

TypeOK ==
    /\ local_disk \in Value
    /\ nfs_disk \in Value
    /\ local_mem_val \in NullValue
    /\ local_db_val \in Value
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
    /\ local_pc = "Init"
    /\ current_req = 30

    /\ job_map = [id \in RequestID |-> nil]
    /\ db = [val |-> 20]

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
    /\ local_unchanged


UpdateLocalDB ==
    /\ local_pc = "UpdateLocalDB" \* TODO handle outbox
    /\ local_pc' = "Init"
    /\ local_db_val' = local_mem_val
    /\ local_mem_val' = nil
    /\ UNCHANGED current_req
    /\ UNCHANGED sync_vars
    /\ UNCHANGED disk_vars
    /\ local_unchanged

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
    /\ job_map[id] # nil
    /\ job_map[id].status = "Finished"
    /\ job_map' = [job_map EXCEPT ![id] = nil]
    /\ IF db.val < job_map[id].val
        THEN db' = [db EXCEPT !.val = job_map[id].val]
        ELSE UNCHANGED db
    /\ UNCHANGED nfs_disk
    /\ UNCHANGED local_vars
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
    \/ Terminated

Spec == Init /\ [][Next]_vars

----------------------------------------------------------------

DataMatchInv ==
    StopCond =>
        /\ local_disk = nfs_disk
        /\ local_disk = local_db_val
        /\ local_disk = db.val

====

------ MODULE DirectSync ----
EXTENDS TLC, Naturals, Sequences

CONSTANTS max_val, nil

VARIABLES
    local_disk, nfs_disk,
    local_mem_val, local_db_val, local_pc,
    current_req,
    job_map

vars == <<
    local_disk, nfs_disk,
    local_mem_val, local_db_val, local_pc,
    current_req,
    job_map
>>

disk_vars == <<local_disk, nfs_disk>>

local_vars == <<local_disk, local_mem_val, local_db_val, local_pc, current_req>>

sync_vars == <<job_map>>

----------------------------------------------------------------

Value == 20..max_val

NullValue == (Value \ {20}) \union {nil}

RequestID == 30..34

Job == [
    id: RequestID,
    status: {"Pending", "Syncing", "Finished"}
]

NullJob == Job \union {nil}

----------------------------------------------------------------

TypeOK ==
    /\ local_disk \in Value
    /\ nfs_disk \in Value
    /\ local_mem_val \in NullValue
    /\ local_db_val \in Value
    /\ local_pc \in {"Init", "SendSync", "UpdateLocalDB"}
    /\ current_req \in RequestID

    /\ job_map \in [RequestID -> NullJob]


Init ==
    /\ local_disk = 20
    /\ nfs_disk = 20
    /\ local_mem_val = nil
    /\ local_db_val = 20
    /\ local_pc = "Init"
    /\ current_req = 30

    /\ job_map = [id \in RequestID |-> nil]

----------------------------------------------------------------

UpdateLocalDisk ==
    /\ local_disk < max_val
    /\ local_disk' = local_disk + 1
    /\ UNCHANGED local_pc
    /\ UNCHANGED local_mem_val
    /\ UNCHANGED local_db_val
    /\ UNCHANGED nfs_disk
    /\ UNCHANGED current_req
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


SendSync ==
    LET
        init_job == [
            id |-> current_req,
            status |-> "Pending"
        ]
    IN
    /\ local_pc = "SendSync"
    /\ local_pc' = "UpdateLocalDB"
    /\ job_map' = [job_map EXCEPT ![current_req] = init_job]
    /\ UNCHANGED current_req
    /\ UNCHANGED disk_vars
    /\ UNCHANGED local_mem_val
    /\ UNCHANGED local_db_val


UpdateLocalDB ==
    /\ local_pc = "UpdateLocalDB" \* TODO handle outbox
    /\ local_pc' = "Init"
    /\ local_db_val' = local_mem_val
    /\ local_mem_val' = nil
    /\ UNCHANGED current_req
    /\ UNCHANGED sync_vars
    /\ UNCHANGED disk_vars

----------------------------------------------------------------

StartSync(id) ==
    /\ job_map[id] # nil
    /\ job_map[id].status = "Pending"
    /\ job_map' = [job_map EXCEPT
            ![id].status = "Syncing"
        ]
    /\ UNCHANGED nfs_disk
    /\ UNCHANGED local_vars


FinishSync(id) ==
    /\ job_map[id] # nil
    /\ job_map[id].status = "Syncing"
    /\ nfs_disk' = local_disk
    /\ job_map' = [job_map EXCEPT
            ![id].status = "Finished"
        ]
    /\ UNCHANGED local_vars

----------------------------------------------------------------

StopCond ==
    /\ local_pc = "Init"
    /\ local_db_val = local_disk
    /\ \A id \in RequestID:
        job_map[id] # nil => job_map[id].status = "Finished"

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
    \/ Terminated

Spec == Init /\ [][Next]_vars

----------------------------------------------------------------

DataMatchInv ==
    StopCond =>
        /\ local_disk = nfs_disk
        /\ local_disk = local_db_val

====

------ MODULE USS ----
EXTENDS TLC, Sequences, Naturals, FiniteSets

Range(f) == {f[x]: x \in DOMAIN f}

--------------------------------------------------------------------------

CONSTANTS nil, max_actions

VARIABLES
    replicas, sync_jobs, next_val, num_actions,
    master_replicas, slave_events, deleted_spans,
    source_map

const_vars == <<source_map>>

vars == <<
    replicas, sync_jobs, next_val, num_actions,
    master_replicas, slave_events, deleted_spans,
    const_vars
>>

--------------------------------------------------------------------------

SpanID == 21..23

primary_span == 21

NullSpanID == SpanID \union {nil}

possible_source_map ==
    LET
        cond(m) ==
            \A span \in SpanID:
                IF span # primary_span THEN
                    m[span] \in primary_span..(span - 1)
                ELSE
                    m[span] = nil
    IN
    {m \in [SpanID -> NullSpanID]: cond(m)}


Value == 30..39

NullValue == Value \union {nil}

ReplicaID == DOMAIN replicas

Version == 0..10

Generation == 0..10

Replica == [
    id: ReplicaID,
    span: SpanID,
    type: {"Primary", "Readonly"},
    status: {"Empty", "Writing", "Written"},
    value: NullValue,
    delete_status: {"NoAction", "NeedDelete", "CanDelete", "Deleting", "Deleted"},
    write_version: Version,
    generation: Generation,
    hard_deleted: BOOLEAN,

    slave_status: {nil, "SlaveWriting", "SlaveWriteCompleted", "SlaveDeleted"},
    slave_version: Version,
    slave_generation: Generation
]

SyncJobID == DOMAIN sync_jobs

SyncJob == [
    src_id: ReplicaID,
    dst_id: ReplicaID,
    status: {"Pending", "Ready", "Succeeded", "Waiting"}
]

SlaveEvent ==
    LET
        write_event == [
            type: {"Write"},
            repl_id: ReplicaID
        ]

        write_completed_event == [
            type: {"WriteComplete"},
            repl_id: ReplicaID,
            version: Version
        ]
    IN
    write_event \union write_completed_event

--------------------------------------------------------------------------

TypeOK ==
    /\ replicas \in Seq(Replica)
    /\ sync_jobs \in Seq(SyncJob)
    /\ source_map \in possible_source_map
    /\ next_val \in Value
    /\ num_actions \in 0..max_actions
    /\ master_replicas \in Seq(Replica)
    /\ slave_events \in Seq(SlaveEvent)
    /\ deleted_spans \subseteq SpanID


Init ==
    /\ replicas = <<>>
    /\ sync_jobs = <<>>
    /\ source_map \in possible_source_map
    /\ next_val = 30
    /\ num_actions = 0
    /\ master_replicas = <<>>
    /\ slave_events = <<>>
    /\ deleted_spans = {}

--------------------------------------------------------------------------

is_replica_deleted(id) ==
    /\ replicas[id].delete_status # "NoAction"
    /\ replicas[id].delete_status # "NeedDelete"


get_replicas_with_span(span) ==
    LET
        filter_fn(r) ==
            /\ r.span = span
            /\ ~(is_replica_deleted(r.id) /\ r.hard_deleted)
    IN
    SelectSeq(replicas, filter_fn)


allow_to_add_span(span) ==
    \/ span = primary_span
    \/ /\ span # primary_span
       /\ get_replicas_with_span(span - 1) # <<>>


find_source_replica(span) ==
    LET
        list01 == get_replicas_with_span(span)
        list02 == get_replicas_with_span(source_map[span])
    IN
    IF list01 # <<>> THEN
        list01[1].id
    ELSE IF list02 # <<>> THEN
        list02[1].id
    ELSE
        nil


inc_action ==
    /\ num_actions < max_actions
    /\ num_actions' = num_actions + 1

core_unchanged ==
    /\ UNCHANGED next_val
    /\ UNCHANGED const_vars
    /\ UNCHANGED slave_events
    /\ UNCHANGED master_replicas


AddReplica(span) ==
    LET
        repl_type ==
            IF replicas = <<>>
                THEN "Primary"
                ELSE "Readonly"

        new_id == Len(replicas) + 1

        new_repl == [
            id |-> new_id,
            span |-> span,
            type |-> repl_type,
            status |-> "Empty",
            value |-> nil,
            delete_status |-> "NoAction",
            write_version |-> 0,
            generation |-> 1,
            hard_deleted |-> FALSE,

            slave_status |-> nil,
            slave_version |-> 0,
            slave_generation |-> 1
        ]

        src_id == find_source_replica(span)

        job_status ==
            IF replicas[src_id].status = "Written" THEN
                IF is_replica_deleted(src_id) THEN
                    "Pending"
                ELSE
                    "Ready"
            ELSE
                "Pending"

        new_job == [
            src_id |-> src_id,
            dst_id |-> new_id,
            status |-> job_status
        ]

        add_new_job ==
            sync_jobs' = Append(sync_jobs, new_job)
    IN
    /\ allow_to_add_span(span)
    /\ inc_action

    /\ replicas' = Append(replicas, new_repl)
    /\ IF repl_type = "Primary"
        THEN UNCHANGED sync_jobs
        ELSE add_new_job

    /\ UNCHANGED deleted_spans
    /\ core_unchanged


trigger_sync_from_replica(id, input_jobs) ==
    LET
        allow_trigger(job_id) ==
            LET
                dst_id == input_jobs[job_id].dst_id
                dst_repl == replicas[dst_id]
            IN
            /\ input_jobs[job_id].src_id = id
            /\ ~(dst_repl.hard_deleted /\ is_replica_deleted(dst_id))

        is_replica_deleting(job_id) ==
            LET
                dst_id == input_jobs[job_id].dst_id
                dst_repl == replicas[dst_id]
            IN
                dst_repl.delete_status = "Deleting"

        updated_status(job_id) ==
            IF is_replica_deleting(job_id)
                THEN "Waiting"
                ELSE "Ready"

        update_job(job_id, old) ==
            IF allow_trigger(job_id)
                THEN [old EXCEPT !.status = updated_status(job_id)]
                ELSE old
    IN
        [job_id \in SyncJobID |->
            update_job(job_id, input_jobs[job_id])]


num_non_finished_sync_job(repl_id, input_jobs) ==
    LET
        job_cond(job_id) ==
            /\ \/ input_jobs[job_id].src_id = repl_id
               \/ input_jobs[job_id].dst_id = repl_id
            /\ input_jobs[job_id].status # "Succeeded"

        job_set == {job_id \in SyncJobID: job_cond(job_id)}
    IN
        Cardinality(job_set)


set_replica_delete_status(ids, input_replicas, input_jobs) ==
    LET
        allow_update(id, old) ==
            /\ id \in ids
            /\ old.status = "Written"
            /\ old.delete_status = "NeedDelete"
            /\ num_non_finished_sync_job(id, input_jobs) = 0

        update(id, old) ==
            IF allow_update(id, old)
                THEN [old EXCEPT !.delete_status = "CanDelete"]
                ELSE old
    IN
        [id \in DOMAIN input_replicas |-> update(id, input_replicas[id])]


new_delete_status(old) ==
    IF old = "NoAction"
        THEN old
        ELSE "NeedDelete"

updatePrimary(id, version) ==
    LET
        updated == [replicas EXCEPT
                ![id].status = "Written",
                ![id].write_version = version,
                ![id].delete_status = new_delete_status(@)
            ]
    IN
        /\ sync_jobs' = trigger_sync_from_replica(id, sync_jobs)
        /\ replicas' = set_replica_delete_status({id}, updated, sync_jobs')

HandleSlaveEvent ==
    LET
        e == slave_events[1]
        id == e.repl_id

        handle_writing ==
            /\ e.type = "Write"
            /\ replicas' = [replicas EXCEPT ![id].status = "Writing"]
            /\ UNCHANGED sync_jobs

        handle_write_completed ==
            /\ e.type = "WriteComplete"
            /\ updatePrimary(id, e.version)
    IN
    /\ slave_events # <<>>
    /\ slave_events' = Tail(slave_events)
    /\ \/ handle_writing
       \/ handle_write_completed

    /\ UNCHANGED next_val
    /\ UNCHANGED num_actions
    /\ UNCHANGED master_replicas
    /\ UNCHANGED const_vars
    /\ UNCHANGED deleted_spans

--------------------------------------------------------------------------

doFinishJob(job_id) ==
    LET
        job == sync_jobs[job_id]
        src_id == job.src_id
        dst_id == job.dst_id

        updated == [replicas EXCEPT
            ![dst_id].status = "Written",
            ![dst_id].value = replicas[src_id].value,
            ![dst_id].delete_status = new_delete_status(@)
        ]

        set_finished == [sync_jobs EXCEPT ![job_id].status = "Succeeded"]
    IN
    /\ sync_jobs[job_id].status = "Ready"
    /\ UNCHANGED num_actions

    /\ sync_jobs' = trigger_sync_from_replica(dst_id, set_finished)
    /\ replicas' = set_replica_delete_status({src_id, dst_id}, updated, sync_jobs')

    /\ UNCHANGED deleted_spans
    /\ core_unchanged

FinishJob ==
    \E job_id \in SyncJobID:
        doFinishJob(job_id)

--------------------------------------------------------------------------

AddDeleteRule(span) ==
    /\ span \notin deleted_spans
    /\ inc_action

    /\ deleted_spans' = deleted_spans \union {span}
    /\ UNCHANGED replicas
    /\ UNCHANGED sync_jobs

    /\ core_unchanged


doApplyDeleteRule(span, id) ==
    LET
        updated == [replicas EXCEPT ![id].delete_status = "NeedDelete"]
    IN
    /\ replicas[id].delete_status = "NoAction"
    /\ replicas[id].span = span

    /\ replicas' = set_replica_delete_status({id}, updated, sync_jobs)

    /\ UNCHANGED sync_jobs
    /\ UNCHANGED deleted_spans

ApplyDeleteRule(span) ==
    /\ span \in deleted_spans
    /\ \E id \in ReplicaID: doApplyDeleteRule(span, id)
    /\ UNCHANGED num_actions
    /\ core_unchanged


get_sync_job_of(id) ==
    LET
        job_set == {job_id \in SyncJobID: sync_jobs[job_id].dst_id = id}
    IN
        IF job_set = {}
            THEN nil
            ELSE CHOOSE job_id \in job_set: TRUE

sync_job_is_waiting(job_id) ==
    LET
        job == sync_jobs[job_id]
    IN
    /\ job_id # nil
    /\ job.status = "Waiting"


doUpdateToDeleting(id) ==
    LET
        normal_flow ==
            /\ replicas' = [replicas EXCEPT
                    ![id].delete_status = "Deleting",
                    ![id].slave_status = "SlaveDeleted"
                ]

        update_to_need_delete ==
            /\ replicas' = [replicas EXCEPT
                    ![id].delete_status = new_delete_status(@)
                ]

        when_is_primary ==
            IF replicas[id].slave_version = replicas[id].write_version
                THEN normal_flow
                ELSE update_to_need_delete
        
        job_id == get_sync_job_of(id)
        job == sync_jobs[job_id]

        when_is_readonly ==
            IF job.status # "Succeeded"
                THEN update_to_need_delete
                ELSE replicas' = [replicas EXCEPT ![id].delete_status = "Deleting"]
    IN
    /\ replicas[id].delete_status = "CanDelete"
    /\ IF replicas[id].type = "Primary"
        THEN when_is_primary
        ELSE when_is_readonly

    /\ UNCHANGED sync_jobs
    /\ UNCHANGED deleted_spans
    /\ UNCHANGED num_actions
    /\ core_unchanged

UpdateToDeleting ==
    \E id \in ReplicaID: doUpdateToDeleting(id)


doDeleteReplica(id) ==
    LET
        when_normal ==
            /\ replicas' = [replicas EXCEPT
                    ![id].delete_status = "Deleted",
                    ![id].value = nil,
                    ![id].generation = @ + 1
                ]
            /\ UNCHANGED sync_jobs

        job_id == get_sync_job_of(id)

        when_waiting ==
            /\ sync_jobs' = [sync_jobs EXCEPT ![job_id].status = "Ready"]
            /\ replicas' = [replicas EXCEPT
                    ![id].delete_status = new_delete_status(@),
                    ![id].status = "Empty",
                    ![id].value = nil
                ]
    IN
    /\ replicas[id].delete_status = "Deleting"
    /\ IF sync_job_is_waiting(job_id)
        THEN when_waiting
        ELSE when_normal

    /\ UNCHANGED deleted_spans
    /\ UNCHANGED num_actions
    /\ core_unchanged

DeleteReplica ==
    \E id \in ReplicaID: doDeleteReplica(id)

--------------------------------------------------------------------------

doRemoveExtraReplica(r) ==
    LET
        id == r.id
        job_id == get_sync_job_of(id)
        job == sync_jobs[job_id]

        is_empty_cond ==
            /\ r.status = "Empty"
            /\ job.status = "Pending"

        when_empty ==
            /\ replicas' = [replicas EXCEPT
                    ![id].delete_status = "Deleted",
                    ![id].status = "Written",
                    ![id].hard_deleted = TRUE
                ]
        
        new_status ==
            IF is_replica_deleted(id)
                THEN r.delete_status
                ELSE "NeedDelete"

        updated == [replicas EXCEPT
                ![id].delete_status = new_status,
                ![id].hard_deleted = TRUE
            ]

        when_written ==
            /\ replicas' = set_replica_delete_status({id}, updated, sync_jobs)
    IN
    /\ r.type = "Readonly" \* TODO allow primary too
    /\ inc_action
    /\ IF is_empty_cond
        THEN when_empty
        ELSE when_written

    /\ UNCHANGED deleted_spans
    /\ UNCHANGED sync_jobs
    /\ core_unchanged

RemoveExtraReplica(span) ==
    LET
        repl_list == get_replicas_with_span(span)
        repl_set == Range(repl_list)
    IN
    /\ Len(repl_list) > 1
    /\ \E r \in repl_set: doRemoveExtraReplica(r)

--------------------------------------------------------------------------

slave_unchanged ==
    /\ UNCHANGED sync_jobs
    /\ UNCHANGED const_vars
    /\ UNCHANGED master_replicas
    /\ UNCHANGED deleted_spans


slaveDoWrite(id) ==
    LET
        repl == master_replicas[id]

        event == [
            type |-> "Write",
            repl_id |-> id
        ]

        when_nil ==
            /\ replicas[id].slave_status = nil
            /\ UNCHANGED num_actions

        when_write_completed ==
            /\ replicas[id].slave_status = "SlaveWriteCompleted"
            /\ inc_action

        when_fully_deleted ==
            /\ repl.delete_status = "Deleted"
            /\ repl.generation > replicas[id].slave_generation
            /\ inc_action
    IN
    /\ id \in DOMAIN master_replicas
    /\ repl.type = "Primary"
    /\ \/ when_nil
       \/ when_write_completed
       \/ when_fully_deleted

    /\ slave_events' = Append(slave_events, event)
    /\ replicas' = [replicas EXCEPT
            ![id].slave_status = "SlaveWriting",
            ![id].slave_version = @ + 1,
            ![id].slave_generation = repl.generation
        ]

    /\ UNCHANGED next_val
    /\ slave_unchanged

SlaveWrite ==
    \E id \in ReplicaID: slaveDoWrite(id)


SlaveWriteComplete ==
    \E id \in DOMAIN master_replicas:
        LET
            event == [
                type |-> "WriteComplete",
                repl_id |-> id,
                version |-> replicas'[id].slave_version
            ]
        IN
        /\ master_replicas[id].type = "Primary"
        /\ replicas[id].slave_status = "SlaveWriting"

        /\ next_val' = next_val + 1
        /\ replicas' = [replicas EXCEPT
                ![id].slave_status = "SlaveWriteCompleted",
                ![id].slave_version = @ + 1,
                ![id].value = next_val'
            ]
        /\ slave_events' = Append(slave_events, event)

        /\ UNCHANGED num_actions
        /\ slave_unchanged

--------------------------------------------------------------------------

MasterSync ==
    /\ master_replicas # replicas
    /\ master_replicas' = replicas

    /\ UNCHANGED replicas
    /\ UNCHANGED next_val
    /\ UNCHANGED sync_jobs
    /\ UNCHANGED num_actions
    /\ UNCHANGED const_vars
    /\ UNCHANGED slave_events
    /\ UNCHANGED deleted_spans

--------------------------------------------------------------------------

replicaTerminateCond(repl) ==
    /\ repl.type = "Primary" =>
        \/ repl.slave_status = "SlaveWriteCompleted"
        \/ repl.slave_status = "SlaveDeleted"

    /\ \/ repl.delete_status = "NoAction"
       \/ repl.delete_status = "Deleted"
       \/ /\ repl.status = "Empty"
          /\ repl.delete_status = "NeedDelete"

syncJobTerminateCond(job) ==
    \/ job.status = "Succeeded"
    \/ job.status = "Pending"

TerminateCond ==
    /\ slave_events = <<>>
    /\ \A id \in ReplicaID: replicaTerminateCond(replicas[id])
    /\ \A job_id \in SyncJobID: syncJobTerminateCond(sync_jobs[job_id])
    /\ \A span \in SpanID: ~(ENABLED ApplyDeleteRule(span))


Terminated ==
    /\ TerminateCond
    /\ UNCHANGED vars


Next ==
    \/ \E span \in SpanID:
        \/ AddReplica(span)
        \/ AddDeleteRule(span)
        \/ ApplyDeleteRule(span)
        \/ RemoveExtraReplica(span)

    \/ UpdateToDeleting
    \/ DeleteReplica

    \/ SlaveWrite
    \/ SlaveWriteComplete
    \/ HandleSlaveEvent

    \/ MasterSync
    \/ FinishJob
    \/ Terminated

Spec == Init /\ [][Next]_vars

--------------------------------------------------------------------------

AtMostOnePrimary ==
    LET
        primary_set == {id \in ReplicaID: replicas[id].type = "Primary"}
    IN
        Cardinality(primary_set) <= 1


getPrimaryRepl ==
    LET
        primary_set == {id \in ReplicaID: replicas[id].type = "Primary"}
    IN
        CHOOSE id \in primary_set: TRUE


ReadonlyReplicaAlwaysHaveSyncJob ==
    LET
        exist_job_dst_id(dst_id) ==
            \E job_id \in SyncJobID: sync_jobs[job_id].dst_id = dst_id
    IN
        \A id \in ReplicaID:
            replicas[id].type = "Readonly" <=> exist_job_dst_id(id)


WhenTerminatedAllReplicasWritten ==
    LET
        fully_written(repl) ==
            /\ repl.status = "Written"
            /\ repl.value = next_val
            /\ repl.delete_status = "NoAction"

        is_still_empty(repl) ==
            /\ repl.status = "Empty"
            /\ repl.value = nil
            /\ \/ repl.delete_status = "NoAction"
               \/ repl.delete_status = "NeedDelete"

        when_no_deletion(repl) ==
            IF deleted_spans = {}
                THEN fully_written(repl)
                ELSE \/ fully_written(repl)
                     \/ is_still_empty(repl)

        fully_deleted(repl) ==
            /\ repl.delete_status = "Deleted"
            /\ repl.status = "Written"
            /\ repl.value = nil

        when_has_delete_rule(repl) ==
            IF repl.type = "Primary" THEN
                fully_deleted(repl)
            ELSE
                \/ fully_deleted(repl)
                \/ is_still_empty(repl)

        cond(r) ==
            IF r.hard_deleted THEN
                /\ r.status = "Written"
                /\ r.delete_status = "Deleted"
                /\ r.value = nil
            ELSE IF r.span \in deleted_spans THEN
                when_has_delete_rule(r)
            ELSE
                when_no_deletion(r)
    IN
    TerminateCond =>
        \A id \in ReplicaID: cond(replicas[id])


SyncJobAndDeleteJobConcurrently ==
    \A id \in ReplicaID:
        LET
            job_cond(job_id) ==
                /\ \/ sync_jobs[job_id].src_id = id
                   \/ sync_jobs[job_id].dst_id = id
                /\ sync_jobs[job_id].status = "Ready"

            job_set == {job_id \in SyncJobID: job_cond(job_id)}

            cond1 == ENABLED doDeleteReplica(id)
            cond2 == job_set # {}
            cond3 == ENABLED slaveDoWrite(id)
        IN
            /\ ~(cond1 /\ cond2)
            /\ ~(cond1 /\ cond3)


ShouldNotSyncToHardDeleted ==
    \A id \in ReplicaID:
        LET
            r == replicas[id]

            pre_cond ==
                /\ r.delete_status = "Deleted"
                /\ r.hard_deleted

            job_id == get_sync_job_of(r.id)
            job == sync_jobs[job_id]

            cond ==
                \/ job.status = "Succeeded"
                \/ job.status = "Pending"
        IN
            pre_cond => cond

====

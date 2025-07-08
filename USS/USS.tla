------ MODULE USS ----
EXTENDS TLC, Sequences, Naturals, FiniteSets

CONSTANTS nil, max_actions

VARIABLES
    replicas, sync_jobs, next_val, num_actions,
    master_replicas, slave_events, deleted_spans, source_map

const_vars == <<source_map>>

vars == <<
    replicas, sync_jobs, next_val, num_actions,
    master_replicas, slave_events, deleted_spans, const_vars
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

Replica == [
    id: ReplicaID,
    span: SpanID,
    type: {"Primary", "Readonly"},
    status: {"Empty", "Writing", "Written"},
    value: NullValue,
    delete_status: {"NoAction", "NeedDelete", "CanDelete", "Deleted"},
    slave_status: {nil, "Writing", "WriteCompleted"}
]

SyncJobID == DOMAIN sync_jobs

SyncJob == [
    src_id: ReplicaID,
    dst_id: ReplicaID,
    status: {"Pending", "Ready", "Succeeded"}
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
            value: Value
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

get_replicas_with_span(span) ==
    LET
        filter_fn(r) == r.span = span
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
            slave_status |-> nil
        ]

        src_id == find_source_replica(span)

        job_status ==
            IF replicas[src_id].status = "Written"
                THEN "Ready"
                ELSE "Pending"

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


trigger_sync_replica(id, input_jobs) ==
    LET
        allow_trigger(job_id) ==
            /\ input_jobs[job_id].src_id = id

        update_job(job_id, old) ==
            IF allow_trigger(job_id)
                THEN [old EXCEPT !.status = "Ready"]
                ELSE old
    IN
        [job_id \in SyncJobID |->
            update_job(job_id, input_jobs[job_id])]


setToCanDelete(ids, input_replicas) ==
    LET
        update_repl(id, old) ==
            IF id \in ids
                THEN [old EXCEPT !.delete_status = "CanDelete"]
                ELSE old
    IN
        [id \in ReplicaID |-> update_repl(id, input_replicas[id])]



updatePrimary(id, val) ==
    LET
        deleted_set ==
            IF replicas[id].delete_status = "NeedDelete"
                THEN {id}
                ELSE {}

        set_written == [replicas EXCEPT
            ![id].status = "Written",
            ![id].value = val
        ]
    IN
    /\ replicas' = setToCanDelete(deleted_set, set_written)
    /\ sync_jobs' = trigger_sync_replica(id, sync_jobs)

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
            /\ updatePrimary(id, e.value)
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

num_non_finished_sync_job_of_replica(repl_id, input_jobs) ==
    LET
        job_cond(job_id) ==
            /\ input_jobs[job_id].src_id = repl_id
            /\ input_jobs[job_id].status # "Succeeded"

        job_set == {job_id \in SyncJobID: job_cond(job_id)}
    IN
        Cardinality(job_set)


set_replica_delete_status(ids, input_replicas, input_jobs) ==
    LET
        allow_update(id, old) ==
            /\ id \in ids
            /\ old.delete_status = "NeedDelete"
            /\ num_non_finished_sync_job_of_replica(id, input_jobs) = 0

        update(id, old) ==
            IF allow_update(id, old)
                THEN [old EXCEPT !.delete_status = "CanDelete"]
                ELSE old
    IN
        [id \in DOMAIN input_replicas |-> update(id, input_replicas[id])]


doFinishJob(job_id) ==
    LET
        job == sync_jobs[job_id]
        src_id == job.src_id
        dst_id == job.dst_id

        updated == [replicas EXCEPT
            ![dst_id].status = "Written",
            ![dst_id].value = replicas[src_id].value
        ]

        set_finished == [sync_jobs EXCEPT ![job_id].status = "Succeeded"]
    IN
    /\ sync_jobs[job_id].status = "Ready"
    /\ UNCHANGED num_actions

    /\ sync_jobs' = trigger_sync_replica(dst_id, set_finished)
    /\ replicas' = set_replica_delete_status({src_id}, updated, sync_jobs')

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


doDeleteReplica(id) ==
    /\ replicas[id].delete_status = "CanDelete"
    /\ replicas' = [replicas EXCEPT ![id].delete_status = "Deleted"]

    /\ UNCHANGED sync_jobs
    /\ UNCHANGED deleted_spans
    /\ UNCHANGED num_actions
    /\ core_unchanged

DeleteReplica ==
    \E id \in ReplicaID: doDeleteReplica(id)

--------------------------------------------------------------------------

slave_unchanged ==
    /\ UNCHANGED num_actions
    /\ UNCHANGED sync_jobs
    /\ UNCHANGED const_vars
    /\ UNCHANGED master_replicas
    /\ UNCHANGED deleted_spans

SlaveWrite ==
    \E id \in DOMAIN master_replicas:
        LET
            event == [
                type |-> "Write",
                repl_id |-> id
            ]
        IN
        /\ master_replicas[id].type = "Primary"
        /\ replicas[id].slave_status = nil

        /\ slave_events' = Append(slave_events, event)
        /\ replicas' = [replicas EXCEPT ![id].slave_status = "Writing"]

        /\ UNCHANGED next_val
        /\ slave_unchanged


SlaveWriteComplete ==
    \E id \in DOMAIN master_replicas:
        LET
            event == [
                type |-> "WriteComplete",
                repl_id |-> id,
                value |-> next_val'
            ]
        IN
        /\ master_replicas[id].type = "Primary"
        /\ replicas[id].slave_status = "Writing"

        /\ next_val' = next_val + 1
        /\ slave_events' = Append(slave_events, event)
        /\ replicas' = [replicas EXCEPT ![id].slave_status = "WriteCompleted"]

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

TerminateCond ==
    /\ slave_events = <<>>
    /\ \A id \in ReplicaID:
        replicas[id].type = "Primary" =>
            replicas[id].slave_status = "WriteCompleted"
    /\ \A job_id \in SyncJobID:
        sync_jobs[job_id].status = "Succeeded"
    /\ \A id \in ReplicaID:
        \/ replicas[id].delete_status = "NoAction"
        \/ replicas[id].delete_status = "Deleted"
    /\ \A span \in SpanID: ~(ENABLED ApplyDeleteRule(span))


Terminated ==
    /\ TerminateCond
    /\ UNCHANGED vars


Next ==
    \/ \E span \in SpanID:
        \/ AddReplica(span)
        \/ AddDeleteRule(span)
        \/ ApplyDeleteRule(span)
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
        when_no_deletion(repl) ==
            /\ repl.status = "Written"
            /\ repl.value = next_val
            /\ repl.delete_status = "NoAction"

        when_has_delete_rule(repl) ==
            /\ repl.delete_status = "Deleted"
    IN
    TerminateCond =>
        \A id \in ReplicaID:
            IF replicas[id].span \in deleted_spans
                THEN when_has_delete_rule(replicas[id])
                ELSE when_no_deletion(replicas[id])

====

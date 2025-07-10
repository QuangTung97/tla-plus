------ MODULE USS ----
EXTENDS TLC, Sequences, Naturals, FiniteSets

Range(f) == {f[x]: x \in DOMAIN f}

--------------------------------------------------------------------------

CONSTANTS nil, max_actions

VARIABLES
    replicas, sync_jobs, next_val, num_actions,
    master_replicas, slave_events,
    deleted_spans, hist_deleted_spans,
    source_map

const_vars == <<source_map>>

vars == <<
    replicas, sync_jobs, next_val, num_actions,
    master_replicas, slave_events,
    deleted_spans, hist_deleted_spans,
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


Value == 30..59

NullValue == Value \union {nil}

ReplicaID == DOMAIN replicas

Version == 0..20

Generation == 0..20

DeleteStatus == {
    "NoAction", "NeedDelete", "CanDelete",
    "ReadyToDelete", "Deleting", "Deleted"
}

Replica == [
    id: ReplicaID,
    span: SpanID,
    type: {"Primary", "Readonly"},
    status: {"Empty", "Writing", "Written"},
    value: NullValue,
    delete_status: DeleteStatus,
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
    /\ hist_deleted_spans \subseteq SpanID
    /\ deleted_spans \subseteq hist_deleted_spans


Init ==
    /\ replicas = <<>>
    /\ sync_jobs = <<>>
    /\ source_map \in possible_source_map
    /\ next_val = 30
    /\ num_actions = 0
    /\ master_replicas = <<>>
    /\ slave_events = <<>>
    /\ deleted_spans = {}
    /\ hist_deleted_spans = {}

--------------------------------------------------------------------------

is_replica_deleted(r) ==
    /\ r.delete_status # "NoAction"
    /\ r.delete_status # "NeedDelete"

is_hard_deleted(r) ==
    /\ r.hard_deleted
    /\ r.delete_status = "Deleted"


do_get_replicas_with_span(input_span, input_replicas, ignored_id) ==
    LET
        filter_non_primary(r) ==
            /\ r.span = input_span
            /\ ~(r.hard_deleted /\ is_replica_deleted(r))
            /\ ignored_id # nil => r.id < ignored_id

        filter_fn(r) ==
            IF input_span = primary_span
                THEN r.type = "Primary"
                ELSE filter_non_primary(r)
    IN
        SelectSeq(input_replicas, filter_fn)


get_replicas_by_span_raw(span) ==
    LET
        filter_fn(r) ==
            r.span = span
    IN
        SelectSeq(replicas, filter_fn)

allow_to_add_span(span) ==
    \/ span = primary_span
    \/ /\ span # primary_span
       /\ get_replicas_by_span_raw(span - 1) # <<>>


find_source_replica(span, input_replicas, repl_id) ==
    LET
        list01 == do_get_replicas_with_span(span, input_replicas, repl_id)
        list02 == do_get_replicas_with_span(source_map[span], input_replicas, nil)
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


compute_new_job_status(src) ==
    IF src.status = "Written" THEN
        IF is_replica_deleted(src) THEN
            "Pending"
        ELSE
            "Ready"
    ELSE
        "Pending"

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

        src_id == find_source_replica(span, replicas', new_id)
        src == replicas'[src_id]

        new_job == [
            src_id |-> src_id,
            dst_id |-> new_id,
            status |-> compute_new_job_status(src)
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
    /\ UNCHANGED hist_deleted_spans
    /\ core_unchanged


is_replica_deleting(r) ==
    /\ is_replica_deleted(r)
    /\ r.delete_status # "Deleted"


trigger_sync_from_replica(id, input_jobs) ==
    LET
        allow_trigger(job) ==
            LET
                dst_id == job.dst_id
                dst_repl == replicas[dst_id]
            IN
            /\ job.src_id = id
            /\ ~is_hard_deleted(dst_repl)

        updated_status(job) ==
            LET
                dst_id == job.dst_id
                dst_repl == replicas[dst_id]
            IN
            IF is_replica_deleting(dst_repl)
                THEN "Waiting"
                ELSE "Ready"

        update_job(old) ==
            IF allow_trigger(old)
                THEN [old EXCEPT !.status = updated_status(old)]
                ELSE old
    IN
        [job_id \in SyncJobID |-> update_job(input_jobs[job_id])]

----------------------------

num_non_finished_sync_job(repl_id, input_jobs) ==
    LET
        job_cond(job_id) ==
            /\ \/ input_jobs[job_id].src_id = repl_id
               \/ input_jobs[job_id].dst_id = repl_id
            /\ input_jobs[job_id].status # "Succeeded"

        job_set == {job_id \in SyncJobID: job_cond(job_id)}
    IN
        Cardinality(job_set)

private_set_replica_delete_status(ids, input_replicas, input_jobs) ==
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

do_set_delete_status(ids, input_replicas, input_jobs) ==
    /\ replicas' = private_set_replica_delete_status(
            ids, input_replicas, input_jobs
        )
    /\ sync_jobs' = input_jobs

----------------------------

new_delete_status(old, repl) ==
    LET
        is_still_deleted ==
            \/ repl.span \in deleted_spans
            \/ repl.hard_deleted
    IN
    IF old = "NoAction" THEN
        "NoAction"
    ELSE IF is_still_deleted THEN
        "NeedDelete"
    ELSE
        "NoAction"

update_to_need_delete(id, input_replicas) ==
    [input_replicas EXCEPT
        ![id].delete_status = new_delete_status(@, input_replicas[id])]


updatePrimary(id, version) ==
    LET
        updated01 == [replicas EXCEPT
            ![id].status = "Written",
            ![id].write_version = version
        ]

        updated == update_to_need_delete(id, updated01)

        jobs_updated == trigger_sync_from_replica(id, sync_jobs)
    IN
        do_set_delete_status({id}, updated, jobs_updated)

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
    /\ UNCHANGED hist_deleted_spans

--------------------------------------------------------------------------

doFinishJob(job_id) ==
    LET
        job == sync_jobs[job_id]
        src_id == job.src_id
        dst_id == job.dst_id

        updated01 == [replicas EXCEPT
            ![dst_id].status = "Written",
            ![dst_id].value = replicas[src_id].value
        ]

        updated == update_to_need_delete(dst_id, updated01)

        set_finished == [sync_jobs EXCEPT ![job_id].status = "Succeeded"]
        jobs_updated == trigger_sync_from_replica(dst_id, set_finished)
    IN
    /\ sync_jobs[job_id].status = "Ready"
    /\ UNCHANGED num_actions

    /\ do_set_delete_status({src_id, dst_id}, updated, jobs_updated)

    /\ UNCHANGED deleted_spans
    /\ UNCHANGED hist_deleted_spans
    /\ core_unchanged

FinishJob ==
    \E job_id \in SyncJobID:
        doFinishJob(job_id)

--------------------------------------------------------------------------

AddDeleteRule(span) ==
    /\ span \notin deleted_spans
    /\ inc_action

    /\ deleted_spans' = deleted_spans \union {span}
    /\ hist_deleted_spans' = hist_deleted_spans \union {span}
    /\ UNCHANGED replicas
    /\ UNCHANGED sync_jobs

    /\ core_unchanged


RemoveDeleteRule(span) ==
    /\ span \in deleted_spans
    /\ inc_action

    /\ deleted_spans' = deleted_spans \ {span}
    /\ UNCHANGED replicas
    /\ UNCHANGED sync_jobs

    /\ UNCHANGED hist_deleted_spans
    /\ core_unchanged

----------------------------

doApplyDeleteRule(span, id) ==
    LET
        updated == [replicas EXCEPT ![id].delete_status = "NeedDelete"]
    IN
    /\ replicas[id].delete_status = "NoAction"
    /\ replicas[id].span = span

    /\ do_set_delete_status({id}, updated, sync_jobs)

    /\ UNCHANGED deleted_spans

ApplyDeleteRule(span) ==
    /\ span \in deleted_spans
    /\ \E id \in ReplicaID: doApplyDeleteRule(span, id)

    /\ UNCHANGED num_actions
    /\ UNCHANGED hist_deleted_spans
    /\ core_unchanged

----------------------------

doUpdateToReadyDelete(id) ==
    /\ replicas[id].delete_status = "CanDelete"
    /\ replicas' = [replicas EXCEPT ![id].delete_status = "ReadyToDelete"]

    /\ UNCHANGED sync_jobs
    /\ UNCHANGED deleted_spans
    /\ UNCHANGED hist_deleted_spans
    /\ UNCHANGED num_actions
    /\ core_unchanged

UpdateToReadyDelete ==
    \E id \in ReplicaID: doUpdateToReadyDelete(id)

----------------------------

get_sync_job_of(id) ==
    LET
        job_set == {job_id \in SyncJobID: sync_jobs[job_id].dst_id = id}
    IN
        IF job_set = {}
            THEN nil
            ELSE CHOOSE job_id \in job_set: TRUE


doUpdateToDeleting(id) ==
    LET
        primary_normal ==
            replicas' = [replicas EXCEPT
                ![id].delete_status = "Deleting",
                ![id].slave_status = "SlaveDeleted",
                ![id].slave_generation = replicas[id].generation
            ]

        when_is_primary ==
            IF replicas[id].slave_version = replicas[id].write_version
                THEN primary_normal
                ELSE replicas' = update_to_need_delete(id, replicas)

        when_is_readonly ==
            replicas' = [replicas EXCEPT
                ![id].delete_status = "Deleting"
            ]
    IN
    /\ replicas[id].delete_status = "ReadyToDelete"
    /\ IF replicas[id].type = "Primary"
        THEN when_is_primary
        ELSE when_is_readonly

    /\ UNCHANGED sync_jobs
    /\ UNCHANGED deleted_spans
    /\ UNCHANGED hist_deleted_spans
    /\ UNCHANGED num_actions
    /\ core_unchanged

UpdateToDeleting ==
    \E id \in ReplicaID: doUpdateToDeleting(id)

----------------------------

rewire_job_of_hard_deleted(repl_ids, input_replicas, input_jobs) ==
    LET
        need_rewire(id) ==
            /\ id \in repl_ids
            /\ is_hard_deleted(input_replicas[id])

        update(old) ==
            LET
                dst_repl == input_replicas[old.dst_id]
                new_src_id == find_source_replica(
                        dst_repl.span, input_replicas, dst_repl.id
                    )
                new_src == input_replicas[new_src_id]

                update_status ==
                    IF old.status = "Pending"
                        THEN compute_new_job_status(new_src)
                        ELSE old.status
            IN
            IF need_rewire(old.src_id)
                THEN [old EXCEPT !.src_id = new_src_id, !.status = update_status]
                ELSE old
    IN
        [job_id \in DOMAIN input_jobs |-> update(input_jobs[job_id])]

switch_primary_from(old_id, new_id, input_replicas) ==
    LET
        update(r) ==
            IF r.id = old_id THEN
                [r EXCEPT !.type = "Readonly"]
            ELSE IF r.id = new_id THEN
                [r EXCEPT !.type = "Primary"]
            ELSE
                r
    IN
        [id \in DOMAIN input_replicas |-> update(input_replicas[id])]

handle_hard_delete_primary(id, updated) ==
    LET
        span == replicas[id].span

        filter_fn(r) ==
            /\ r.span = span
            /\ ~is_hard_deleted(r)

        new_primary_replicas == SelectSeq(updated, filter_fn)

        new_primary_id == new_primary_replicas[1].id

        switched == switch_primary_from(id, new_primary_id, updated)

        new_job_id == get_sync_job_of(new_primary_id)
        jobs_switched == [sync_jobs EXCEPT
            ![new_job_id].src_id = new_primary_id,
            ![new_job_id].dst_id = id,
            ![new_job_id].status = "Succeeded"
        ]
    IN
    /\ replicas' = switched
    /\ sync_jobs' = rewire_job_of_hard_deleted({id}, replicas', jobs_switched)

doDeleteReplica(id) ==
    LET
        updated == [replicas EXCEPT
            ![id].delete_status = "Deleted",
            ![id].value = nil,
            ![id].generation = @ + 1
        ]

        job_id == get_sync_job_of(id)
        is_waiting ==
            /\ job_id # nil
            /\ sync_jobs[job_id].status = "Waiting"
        
        when_waiting ==
            /\ sync_jobs' = [sync_jobs EXCEPT ![job_id].status = "Ready"]
            /\ replicas' = update_to_need_delete(id, updated)

        hard_delete_readonly ==
            /\ replicas' = updated
            /\ sync_jobs' = rewire_job_of_hard_deleted({id}, replicas', sync_jobs)

        when_hard_deleted ==
            IF replicas[id].type = "Primary"
                THEN handle_hard_delete_primary(id, updated)
                ELSE hard_delete_readonly

        when_delete_fully ==
            /\ replicas' = updated
            /\ UNCHANGED sync_jobs

        when_normal ==
            IF is_hard_deleted(updated[id])
                THEN when_hard_deleted
                ELSE when_delete_fully
    IN
    /\ replicas[id].delete_status = "Deleting"
    /\ IF is_waiting
        THEN when_waiting
        ELSE when_normal

    /\ UNCHANGED deleted_spans
    /\ UNCHANGED hist_deleted_spans
    /\ UNCHANGED num_actions
    /\ core_unchanged

DeleteReplica ==
    \E id \in ReplicaID: doDeleteReplica(id)

--------------------------------------------------------------------------

doRemoveExtraReplicaReadonly(r) ==
    LET
        id == r.id
        job_id == get_sync_job_of(id)
        job == sync_jobs[job_id]

        can_delete_right_away ==
            \/ /\ r.status = "Empty"
               /\ job.status = "Pending"
            \/ /\ r.delete_status = "Deleted"
               /\ job.status = "Succeeded"

        update_job_to_succeeded == [sync_jobs EXCEPT ![job_id].status = "Succeeded"]

        when_empty ==
            /\ replicas' = [replicas EXCEPT
                    ![id].delete_status = "Deleted",
                    ![id].status = "Written",
                    ![id].hard_deleted = TRUE
                ]
            /\ sync_jobs' = rewire_job_of_hard_deleted(
                    {id}, replicas', update_job_to_succeeded)

        new_status ==
            IF is_replica_deleting(r)
                THEN r.delete_status
                ELSE "NeedDelete"

        updated == [replicas EXCEPT
                ![id].delete_status = new_status,
                ![id].hard_deleted = TRUE
            ]

        when_written ==
            /\ do_set_delete_status({id}, updated, sync_jobs)
    IN
    /\ r.type = "Readonly"
    /\ inc_action
    /\ IF can_delete_right_away
        THEN when_empty
        ELSE when_written

    /\ UNCHANGED deleted_spans
    /\ UNCHANGED hist_deleted_spans
    /\ core_unchanged

doRemoveExtraReplicaPrimary(r) ==
    LET
        id == r.id

        new_status ==
            IF r.delete_status = "Deleted" THEN
                "CanDelete"
            ELSE IF is_replica_deleting(r) THEN
                r.delete_status
            ELSE
                "NeedDelete"

        updated == [replicas EXCEPT
            ![id].delete_status = new_status,
            ![id].hard_deleted = TRUE
        ]
    IN
    /\ r.type = "Primary"
    /\ inc_action

    /\ do_set_delete_status({id}, updated, sync_jobs)

    /\ UNCHANGED deleted_spans
    /\ UNCHANGED hist_deleted_spans
    /\ core_unchanged

RemoveExtraReplica(span) ==
    LET
        filter_fn(r) ==
            /\ r.span = span
            /\ ~r.hard_deleted

        repl_list == SelectSeq(replicas, filter_fn)
        repl_set == Range(repl_list)
    IN
    /\ Len(repl_list) > 1
    /\ \E r \in repl_set:
        \/ doRemoveExtraReplicaReadonly(r)
        \/ doRemoveExtraReplicaPrimary(r)

--------------------------------------------------------------------------

slave_unchanged ==
    /\ UNCHANGED sync_jobs
    /\ UNCHANGED const_vars
    /\ UNCHANGED master_replicas
    /\ UNCHANGED deleted_spans
    /\ UNCHANGED hist_deleted_spans


slaveDoWrite(id) ==
    LET
        repl == master_replicas[id] \* from USS master instead of core DB

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
    /\ repl.delete_status # "Deleting"
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
    /\ UNCHANGED hist_deleted_spans

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
        \/ RemoveDeleteRule(span)
        \/ ApplyDeleteRule(span)
        \/ RemoveExtraReplica(span)

    \/ UpdateToReadyDelete
    \/ UpdateToDeleting
    \/ DeleteReplica

    \/ SlaveWrite
    \/ SlaveWriteComplete
    \/ HandleSlaveEvent

    \/ MasterSync
    \/ FinishJob
    \/ Terminated

Spec == Init /\ [][Next]_vars

FairSpec == Spec /\ WF_vars(Next)

--------------------------------------------------------------------------

AlwaysTerminated == []<> TerminateCond


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
            /\ ~repl.hard_deleted

        is_still_empty(repl) ==
            /\ repl.status = "Empty"
            /\ repl.value = nil
            /\ ~repl.hard_deleted
            /\ \/ repl.delete_status = "NoAction"
               \/ repl.delete_status = "NeedDelete"

        fully_deleted(repl) ==
            /\ repl.delete_status = "Deleted"
            /\ repl.status = "Written"
            /\ repl.value = nil

        when_no_deletion(repl) ==
            IF hist_deleted_spans = {}
                THEN fully_written(repl)
                ELSE \/ fully_written(repl)
                     \/ is_still_empty(repl)
                     \/ fully_deleted(repl)

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

            job_id == get_sync_job_of(r.id)
            job == sync_jobs[job_id]

            pre_cond ==
                /\ job_id # nil
                /\ r.delete_status = "Deleted"
                /\ r.hard_deleted

            cond ==
                \/ job.status = "Succeeded"
                \/ job.status = "Pending"
        IN
            pre_cond => cond

------------------------

compute_sync_job_closure(repl_ids) ==
    LET
        job_set == {j \in Range(sync_jobs): j.src_id \in repl_ids}
        new_set == {j.dst_id: j \in job_set}
    IN
        repl_ids \union new_set


RECURSIVE get_reachable_replicas_from(_)

get_reachable_replicas_from(repl_ids) ==
    LET
        new_set == compute_sync_job_closure(repl_ids)
    IN
    IF new_set = repl_ids
        THEN repl_ids
        ELSE get_reachable_replicas_from(new_set)

EveryReplicaReachableByPrimary ==
    LET
        pre_cond == Len(replicas) > 0

        filter_fn(r) == r.type = "Primary"
        primary_repl == SelectSeq(replicas, filter_fn)[1]

        all_replicas == {r.id: r \in Range(replicas)}

        cond ==
            /\ primary_repl.type = "Primary"
            /\ get_reachable_replicas_from({primary_repl.id}) = all_replicas
    IN
        pre_cond => cond

------------------------

ReplicaDeleteStatusInv ==
    \A r \in Range(replicas):
        r.delete_status = "Deleted" => r.status \in {"Writing", "Written"}


NoSyncJobShouldSourceFromHardDeleted ==
    \A j \in Range(sync_jobs): ~is_hard_deleted(replicas[j.src_id])

------------------------

syncJobStatusStepInv ==
    \A job_id \in SyncJobID:
        /\ sync_jobs[job_id].status = "Ready"
            => sync_jobs'[job_id].status \in {"Ready", "Succeeded", "Waiting"}
        /\ sync_jobs[job_id].status = "Waiting"
            => sync_jobs'[job_id].status \in {"Waiting", "Ready"}

SyncJobStatusProperty ==
    [][syncJobStatusStepInv]_sync_jobs

------------------------

deleteStatusStepInv ==
    \A id \in ReplicaID:
        replicas[id].delete_status = "Deleting"
            => replicas'[id].delete_status \in {
                    "Deleting", "Deleted", "NeedDelete", "NoAction"
                }

DeleteStatusProperty == [][deleteStatusStepInv]_replicas

------------------------

PrimaryReplicaInv ==
    \A r \in Range(replicas):
        r.type = "Primary" => r.span = primary_span

------------------------

SyncJobsAlwaysSyncFromWritten ==
    \A j \in Range(sync_jobs):
        j.status \in {"Ready", "Waiting"} =>
            /\ replicas[j.src_id].status \in {"Written", "Writing"}
            /\ replicas[j.src_id].delete_status # "Deleted"

--------------------------------------------------------------------------

InverseHardDeletedInv ==
    \A r \in Range(replicas): ~r.hard_deleted

====

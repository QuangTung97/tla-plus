------ MODULE USS ----
EXTENDS TLC, Sequences, Naturals, FiniteSets

CONSTANTS nil, max_actions

VARIABLES replicas, sync_jobs, source_map, next_val, num_actions

const_vars == <<source_map>>

vars == <<replicas, sync_jobs, next_val, num_actions, const_vars>>

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
    status: {"Empty", "Writting", "Written"},
    value: NullValue,
    delete_status: {"NoAction", "NeedDelete", "CanDelete", "Ready", "Deleted"}
]

SyncJobID == DOMAIN sync_jobs

SyncJob == [
    src_id: ReplicaID,
    dst_id: ReplicaID,
    status: {"Pending", "Ready", "Succeeded"}
]

--------------------------------------------------------------------------

TypeOK ==
    /\ replicas \in Seq(Replica)
    /\ sync_jobs \in Seq(SyncJob)
    /\ source_map \in possible_source_map
    /\ next_val \in Value
    /\ num_actions \in 0..max_actions


Init ==
    /\ replicas = <<>>
    /\ sync_jobs = <<>>
    /\ source_map \in possible_source_map
    /\ next_val = 30
    /\ num_actions = 0

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
            delete_status |-> "NoAction"
        ]

        new_job == [
            src_id |-> find_source_replica(span),
            dst_id |-> new_id,
            status |-> "Pending"
        ]

        add_new_job ==
            sync_jobs' = Append(sync_jobs, new_job)
    IN
    /\ allow_to_add_span(span)
    /\ num_actions < max_actions
    /\ num_actions' = num_actions + 1

    /\ replicas' = Append(replicas, new_repl)
    /\ IF repl_type = "Primary"
        THEN UNCHANGED sync_jobs
        ELSE add_new_job

    /\ UNCHANGED next_val
    /\ UNCHANGED const_vars

--------------------------------------------------------------------------

TerminateCond ==
    /\ TRUE

Terminated ==
    /\ TerminateCond
    /\ UNCHANGED vars


Next ==
    \/ \E span \in SpanID:
        \/ AddReplica(span)
    \/ Terminated

Spec == Init /\ [][Next]_vars

--------------------------------------------------------------------------

AtMostOnePrimary ==
    LET
        primary_set == {id \in ReplicaID: replicas[id].type = "Primary"}
    IN
        Cardinality(primary_set) <= 1


ReadonlyReplicaAlwaysHaveSyncJob ==
    LET
        exist_job_dst_id(dst_id) ==
            \E job_id \in SyncJobID: sync_jobs[job_id].dst_id = dst_id
    IN
        \A id \in ReplicaID:
            replicas[id].type = "Readonly" <=> exist_job_dst_id(id)

====

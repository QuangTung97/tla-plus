---- MODULE ScheduleLogic ----
EXTENDS TLC, Naturals

CONSTANTS Job, nil, max_rerun, max_db_config, max_failure

VARIABLES
    db_config, db_epoch, mem_epoch,
    db_job, mem_job, scheduling_set, running_set,
    pc, local_job, local_version, local_epoch,
    job_pc,
    background_pc, background_job,
    num_rerun, num_failure

vars == <<
    db_config, db_epoch, mem_epoch,
    db_job, mem_job, scheduling_set, running_set,
    pc, local_job, local_version, local_epoch,
    job_pc,
    background_pc, background_job,
    num_rerun, num_failure
>>

-------------------------------------------------------------

Config == 10..19

Epoch == 21..29
NullEpoch == Epoch \union {nil}
ZeroEpoch == Epoch \union {0}

Status == {"Ready", "Scheduled", "Finished"}

NullJob == Job \union {nil}

JobVersion == 31..39
NullVersion == JobVersion \union {nil}

DBJob == [
    status: Status,
    is_running: BOOLEAN,
    config: Config,
    epoch: ZeroEpoch,
    version: JobVersion
]
NullDBJob == DBJob \union {nil}

MemJob == [
    config: Config,
    version: JobVersion,
    need_schedule: BOOLEAN
]
NullMemJob == MemJob \union {nil}

PC == {
    "Init", "GetNextJob",
    "ScheduleMemJob",
    "UpdateToScheduled",
    "UpdateRunningSet",
    "UpdateJobEpoch"
}

-------------------------------------------------------------

TypeOK ==
    /\ db_config \in Config
    /\ db_epoch \in Epoch \union {20}
    /\ db_job \in [Job -> NullDBJob]

    /\ mem_epoch \in NullEpoch
    /\ mem_job \in [Job -> NullMemJob]
    /\ scheduling_set \subseteq Job
    /\ running_set \subseteq Job

    /\ pc \in PC
    /\ local_job \in NullJob
    /\ local_version \in NullVersion
    /\ local_epoch \in NullEpoch

    /\ job_pc \in [Job -> {"Init", "Running", "Terminated"}]

    /\ background_pc \in {"Init", "UpdateToScheduled", "UpdateRunningSet"}
    /\ background_job \in NullJob

    /\ num_rerun \in 0..max_rerun
    /\ num_failure \in 0..max_failure

Init ==
    /\ db_config = 10
    /\ db_epoch = 20
    /\ db_job = [j \in Job |-> nil]

    /\ mem_epoch = nil
    /\ mem_job = [j \in Job |-> nil]
    /\ scheduling_set = {}
    /\ running_set = {}

    /\ pc = "Init"
    /\ local_job = nil
    /\ local_version = nil
    /\ local_epoch = nil

    /\ job_pc = [j \in Job |-> "Init"]

    /\ background_pc = "Init"
    /\ background_job = nil

    /\ num_rerun = 0
    /\ num_failure = 0

-------------------------------------------------------------

jobUnchanged ==
    /\ UNCHANGED <<mem_epoch, mem_job, scheduling_set, running_set>>
    /\ UNCHANGED <<pc, local_job, local_version, local_epoch>>
    /\ UNCHANGED job_pc
    /\ UNCHANGED <<background_pc, background_job>>
    /\ UNCHANGED num_failure

StartJob(j) ==
    LET
        init_job == [
            status |-> "Ready",
            is_running |-> FALSE,
            config |-> db_config,
            epoch |-> 0,
            version |-> 31
        ]
    IN
    /\ db_job[j] = nil
    /\ db_job' = [db_job EXCEPT ![j] = init_job]
    /\ UNCHANGED db_config
    /\ UNCHANGED db_epoch
    /\ UNCHANGED num_rerun
    /\ jobUnchanged

--------------------------

ReRunJob(j) ==
    /\ num_rerun < max_rerun
    /\ num_rerun' = num_rerun + 1
    /\ db_job[j] # nil
    /\ db_job[j].status # "Ready"
    /\ db_job' = [db_job EXCEPT
            ![j].status = "Ready",
            ![j].version = @ + 1,
            ![j].epoch = 0
        ]
    /\ UNCHANGED db_config
    /\ UNCHANGED db_epoch
    /\ jobUnchanged

-------------------------------------------------------------

mainUnchanged ==
    /\ UNCHANGED db_config
    /\ UNCHANGED <<background_pc, background_job>>
    /\ UNCHANGED num_rerun

--------------------------

LoadConfig ==
    LET
        when_start ==
            /\ db_epoch' = db_epoch + 1
            /\ mem_epoch' = db_epoch'
            /\ mem_job' = [j \in Job |-> nil]

        when_smaller ==
            /\ mem_epoch' = db_epoch
            /\ mem_job' = [j \in Job |-> nil]
            /\ UNCHANGED db_epoch

        when_normal ==
            /\ UNCHANGED mem_job
            /\ UNCHANGED mem_epoch
            /\ UNCHANGED db_epoch
    IN
    /\ pc = "Init"
    /\ pc' = "GetNextJob"
    /\ IF mem_epoch = nil THEN
            when_start
        ELSE IF mem_epoch < db_epoch THEN
            when_smaller
        ELSE
            when_normal
    /\ local_epoch' = mem_epoch'

    /\ UNCHANGED scheduling_set
    /\ UNCHANGED running_set
    /\ UNCHANGED local_job
    /\ UNCHANGED db_job
    /\ UNCHANGED job_pc
    /\ UNCHANGED local_version
    /\ UNCHANGED num_failure
    /\ mainUnchanged

--------------------------

mainNormalUnchanged ==
    /\ UNCHANGED mem_epoch
    /\ UNCHANGED db_epoch
    /\ UNCHANGED num_failure
    /\ mainUnchanged

--------------------------

getNextJobCond(j) ==
    /\ db_job[j] # nil
    /\ db_job[j].status = "Ready"
    /\ db_job[j].epoch < local_epoch

GetNextJob(j) ==
    /\ pc = "GetNextJob"
    /\ getNextJobCond(j)

    /\ pc' = "ScheduleMemJob"
    /\ local_job' = j

    /\ UNCHANGED <<scheduling_set, running_set>>
    /\ UNCHANGED <<local_version, local_epoch>>
    /\ UNCHANGED mem_job
    /\ UNCHANGED db_job
    /\ UNCHANGED job_pc
    /\ mainNormalUnchanged

GetNextJobReloadConfig ==
    /\ pc = "GetNextJob"
    /\ mem_epoch # db_epoch
    /\ pc' = "Init"

    /\ UNCHANGED <<local_version, local_epoch>>
    /\ UNCHANGED <<scheduling_set, running_set>>
    /\ UNCHANGED mem_job
    /\ UNCHANGED local_job
    /\ UNCHANGED db_job
    /\ UNCHANGED job_pc
    /\ mainNormalUnchanged

--------------------------

is_scheduling_or_running(j) ==
    \/ j \in scheduling_set
    \/ j \in running_set

ScheduleMemJob ==
    LET
        j == local_job
        job == db_job[j]

        init_job == [
            config |-> job.config,
            version |-> job.version,
            need_schedule |-> nil
        ]

        base_job ==
            IF mem_job[j] # nil
                THEN [mem_job[j] EXCEPT !.version = job.version]
                ELSE init_job

        scheduling_job == [base_job EXCEPT !.need_schedule = FALSE]
        when_scheduled ==
            /\ ~is_scheduling_or_running(j)
            /\ pc' = "UpdateToScheduled"
            /\ mem_job' = [mem_job EXCEPT ![j] = scheduling_job]
            /\ scheduling_set' = scheduling_set \union {j}
            /\ UNCHANGED local_version

        pending_job == [base_job EXCEPT !.need_schedule = TRUE]
        when_ignore ==
            /\ pc' = "UpdateJobEpoch"
            /\ mem_job' = [mem_job EXCEPT ![j] = pending_job]
            /\ local_version' = job.version
            /\ UNCHANGED scheduling_set
    IN
    /\ pc = "ScheduleMemJob"
    /\ \/ when_scheduled
       \/ when_ignore

    /\ UNCHANGED <<local_job, local_epoch>>
    /\ UNCHANGED db_job
    /\ UNCHANGED job_pc
    /\ UNCHANGED running_set
    /\ mainNormalUnchanged

--------------------------

update_job_scheduled_and_start_success(j) ==
    /\ db_job' = [db_job EXCEPT
            ![j].status = "Scheduled",
            ![j].epoch = 0,
            ![j].is_running = TRUE
        ]
    /\ job_pc' = [job_pc EXCEPT ![j] = "Running"]
    /\ UNCHANGED mem_epoch
    /\ UNCHANGED num_failure

update_job_scheduled_and_start_failed ==
    /\ num_failure < max_failure
    /\ num_failure' = num_failure + 1
    /\ mem_epoch' = nil
    /\ UNCHANGED db_job
    /\ UNCHANGED job_pc

\* TODO add no-op case
update_job_scheduled_and_start(j) ==
    /\ \/ update_job_scheduled_and_start_success(j)
       \/ update_job_scheduled_and_start_failed
    /\ UNCHANGED mem_job
    /\ UNCHANGED <<scheduling_set, running_set>>

UpdateToScheduled ==
    LET
        j == local_job
    IN
    /\ pc = "UpdateToScheduled"
    /\ pc' = "UpdateRunningSet"

    /\ update_job_scheduled_and_start(j)

    /\ UNCHANGED <<local_job, local_version, local_epoch>>
    /\ UNCHANGED db_epoch
    /\ mainUnchanged

--------------------------

clear_local_vars ==
    /\ local_job' = nil
    /\ local_version' = nil
    /\ local_epoch' = nil

clear_mem_job(j) ==
    IF mem_job[j] = nil THEN
        UNCHANGED mem_job
    ELSE IF mem_job[j].need_schedule THEN
        UNCHANGED mem_job
    ELSE
        mem_job' = [mem_job EXCEPT ![j] = nil]

do_update_running_set(j) ==
    /\ scheduling_set' = scheduling_set \ {j}
    /\ running_set' = running_set \union {j}
    /\ clear_mem_job(j)
    /\ UNCHANGED job_pc
    /\ UNCHANGED db_job

UpdateRunningSet ==
    LET
        j == local_job
    IN
    /\ pc = "UpdateRunningSet"
    /\ pc' = "Init"

    /\ do_update_running_set(j)
    /\ clear_local_vars

    /\ mainNormalUnchanged

--------------------------

UpdateJobEpoch ==
    LET
        j == local_job

        allow_update ==
            /\ db_job[j].status = "Ready"
            /\ db_job[j].version = local_version \* TODO remove?
    IN
    /\ pc = "UpdateJobEpoch"
    /\ pc' = "Init"
    /\ IF allow_update
        THEN db_job' = [db_job EXCEPT ![j].epoch = local_epoch]
        ELSE UNCHANGED db_job
    /\ clear_local_vars

    /\ UNCHANGED mem_job
    /\ UNCHANGED job_pc
    /\ UNCHANGED <<scheduling_set, running_set>>
    /\ mainNormalUnchanged

-------------------------------------------------------------

runUnchanged ==
    /\ UNCHANGED <<pc, local_job, local_version, local_epoch>>
    /\ UNCHANGED db_config
    /\ UNCHANGED db_epoch
    /\ UNCHANGED mem_epoch
    /\ UNCHANGED <<background_pc, background_job>>
    /\ UNCHANGED <<scheduling_set, running_set>>
    /\ UNCHANGED <<num_rerun, num_failure>>

FinishRunningJob(j) ==
    LET
        clear_running == [db_job EXCEPT ![j].is_running = FALSE]

        update_to_finished ==
            db_job' = [clear_running EXCEPT
                ![j].status = "Finished",
                ![j].epoch = 0
            ]
    IN
    /\ job_pc[j] = "Running"
    /\ job_pc' = [job_pc EXCEPT ![j] = "Terminated"]
    /\ IF db_job[j].status = "Scheduled"
        THEN update_to_finished
        ELSE db_job' = clear_running

    /\ UNCHANGED mem_job
    /\ runUnchanged

-------------------------------------------------------------

backgroundUnchanged ==
    /\ UNCHANGED <<pc, local_job, local_version, local_epoch>>
    /\ UNCHANGED db_config
    /\ UNCHANGED db_epoch
    /\ UNCHANGED num_rerun

BackgroundSchedule(j) ==
    /\ background_pc = "Init"
    /\ mem_job[j] # nil
    /\ mem_job[j].need_schedule
    /\ ~is_scheduling_or_running(j)

    /\ background_pc' = "UpdateToScheduled"
    /\ background_job' = j
    /\ mem_job' = [mem_job EXCEPT ![j].need_schedule = FALSE]
    /\ scheduling_set' = scheduling_set \union {j}

    /\ UNCHANGED db_job
    /\ UNCHANGED job_pc
    /\ UNCHANGED num_failure
    /\ UNCHANGED <<mem_epoch, running_set>>
    /\ backgroundUnchanged

--------------------------

BackgroundUpdateToScheduled ==
    LET
        j == background_job
    IN
    /\ background_pc = "UpdateToScheduled"
    /\ background_pc' = "UpdateRunningSet"
    /\ update_job_scheduled_and_start(j)

    /\ UNCHANGED background_job
    /\ backgroundUnchanged

--------------------------

BackgroundUpdateRunningSet ==
    LET
        j == background_job
    IN
    /\ background_pc = "UpdateRunningSet"
    /\ background_pc' = "Init"

    /\ do_update_running_set(j)
    /\ background_job' = nil

    /\ UNCHANGED mem_epoch
    /\ UNCHANGED num_failure
    /\ backgroundUnchanged

-------------------------------------------------------------

BackgroundScanRunningSet ==
    LET
        db_running_set ==
            {j \in Job: db_job[j] # nil /\ db_job[j].is_running}

        new_running_set ==
            db_running_set \ scheduling_set
    IN
    /\ running_set # new_running_set
    /\ running_set' = new_running_set

    /\ UNCHANGED db_job
    /\ UNCHANGED mem_job
    /\ UNCHANGED scheduling_set
    /\ UNCHANGED job_pc
    /\ UNCHANGED <<background_pc, background_job>>
    /\ UNCHANGED mem_epoch
    /\ UNCHANGED num_failure
    /\ backgroundUnchanged

-------------------------------------------------------------

IncDBConfig ==
    LET
        update_job(j, old) ==
            IF old = nil
                THEN old
                ELSE [old EXCEPT !.config = db_config']
    IN
    /\ db_config < max_db_config
    /\ db_config' = db_config + 1
    /\ db_job' = [j \in Job |-> update_job(j, db_job[j])]
    /\ db_epoch' = db_epoch + 1

    /\ UNCHANGED <<pc, local_job, local_version, local_epoch>>
    /\ UNCHANGED <<background_pc, background_job>>
    /\ UNCHANGED <<num_rerun, num_failure>>
    /\ UNCHANGED <<mem_epoch, mem_job, scheduling_set, running_set>>
    /\ UNCHANGED job_pc

-------------------------------------------------------------

TerminateCond ==
    /\ pc = "GetNextJob"
    /\ \A j \in Job:
        /\ db_job[j] # nil
        /\ db_job[j].status = "Finished"
        /\ ~db_job[j].is_running
        /\ job_pc[j] = "Terminated"
    /\ background_pc = "Init"
    /\ mem_epoch = db_epoch
    /\ scheduling_set = {}
    /\ running_set = {}

Terminated ==
    /\ TerminateCond
    /\ UNCHANGED vars

--------------------------

Next ==
    \/ \E j \in Job:
        \/ StartJob(j)
        \/ ReRunJob(j)
        \/ GetNextJob(j)
        \/ FinishRunningJob(j)
        \/ BackgroundSchedule(j)
    \/ LoadConfig
    \/ GetNextJobReloadConfig
    \/ ScheduleMemJob
    \/ UpdateToScheduled
    \/ UpdateRunningSet
    \/ UpdateJobEpoch

    \/ BackgroundUpdateToScheduled
    \/ BackgroundUpdateRunningSet
    \/ BackgroundScanRunningSet

    \/ IncDBConfig

    \/ Terminated

\* TODO add restart pc & background pc

Spec == Init /\ [][Next]_vars

-------------------------------------------------------------

NotScanWhenAlreadyInMem ==
    \A j \in Job:
        (ENABLED GetNextJob(j)) =>
            \/ mem_job[j] = nil
            \/ /\ mem_job[j] # nil
               /\ mem_job[j].version < db_job[j].version


TerminateInv ==
    LET
        db_job_cond ==
            \A j \in Job:
                /\ db_job[j].status = "Finished"
                /\ db_job[j].epoch = 0
    IN
    TerminateCond =>
        /\ db_job_cond


SchedulingAndRunningSetDisjointed ==
    scheduling_set \intersect running_set = {}


DBJobStep ==
    LET
        start_step(j) ==
            /\ db_job[j] = nil
            /\ db_job'[j] # nil
            /\ db_job'[j].status = "Ready"

        schedule_step(j) ==
            /\ db_job[j] # nil
            /\ db_job[j].status \in {"Ready", "Finished"}
            /\ db_job'[j].status = "Scheduled"

        update_epoch(j) ==
            /\ db_job[j] # nil
            /\ db_job[j].status = "Ready"
            /\ db_job[j].epoch = 0
            /\ db_job'[j].epoch > 20

        rerun(j) ==
            /\ db_job[j] # nil
            /\ db_job[j].status # "Ready"
            /\ db_job'[j].status = "Ready"
            /\ db_job'[j].epoch = 0
            /\ db_job'[j].version = db_job[j].version + 1

        finish(j) ==
            /\ db_job[j] # nil
            /\ db_job[j].status = "Scheduled"
            /\ db_job'[j].status = "Finished"
            /\ db_job'[j].epoch = 0

        inc_config(j) ==
            /\ db_job[j] # nil
            /\ db_job'[j].status = db_job[j].status
            /\ db_job'[j].config = db_job[j].config + 1

        inc_epoch(j) ==
            /\ db_job[j] # nil
            /\ db_job[j].status = "Ready"
            /\ db_job'[j].status = "Ready"
            /\ db_job'[j].epoch > db_job[j].epoch

        clear_running_step(j) ==
            /\ db_job[j] # nil
            /\ db_job[j].is_running
            /\ db_job'[j].status = db_job[j].status
            /\ ~db_job'[j].is_running
    IN
    \A j \in Job:
        \/ db_job'[j] = db_job[j]
        \/ start_step(j)
        \/ schedule_step(j)
        \/ update_epoch(j)
        \/ rerun(j)
        \/ finish(j)
        \/ inc_config(j)
        \/ inc_epoch(j)
        \/ clear_running_step(j)

DBJobProperty ==
    [][DBJobStep]_db_job


JobIsRunningInv ==
    LET
        pre_cond(j) ==
            /\ db_job[j] # nil
            /\ db_job[j].status = "Finished"
    IN
    \A j \in Job:
        pre_cond(j) => ~db_job[j].is_running


MemConfigAlwaysLatest ==
    LET
        cond(j) ==
            mem_job[j] # nil => mem_job[j].config = db_config
    IN
    db_epoch = mem_epoch =>
        \A j \in Job: cond(j)


DBJobEpochInv ==
    \A j \in Job:
        db_job[j] # nil /\ db_job[j].epoch > 0 =>
            db_job[j].status = "Ready"


MemRunningMatchDBInv ==
    \A j \in Job:
        db_job[j] # nil /\ db_job[j].is_running =>
            is_scheduling_or_running(j)

====

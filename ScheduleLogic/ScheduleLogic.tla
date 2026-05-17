---- MODULE ScheduleLogic ----
EXTENDS TLC, Naturals

CONSTANTS Job, nil, max_rerun, max_db_config

VARIABLES
    db_config, db_epoch, mem_epoch,
    db_job, mem_job,
    pc, local_job, local_version,
    job_pc,
    background_pc, background_job,
    num_rerun

vars == <<
    db_config, db_epoch, mem_epoch,
    db_job, mem_job,
    pc, local_job, local_version,
    job_pc,
    background_pc, background_job,
    num_rerun
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
    config: Config,
    epoch: ZeroEpoch,
    version: JobVersion
]
NullDBJob == DBJob \union {nil}

MemJob == [
    config: Config,
    version: JobVersion,
    need_schedule: BOOLEAN,
    scheduling: BOOLEAN
]
NullMemJob == MemJob \union {nil}

PC == {
    "Init", "GetNextJob",
    "ScheduleMemJob",
    "UpdateToScheduled",
    "UpdateJobEpoch"
}

-------------------------------------------------------------

TypeOK ==
    /\ db_config \in Config
    /\ db_epoch \in Epoch \union {20}
    /\ db_job \in [Job -> NullDBJob]

    /\ mem_epoch \in NullEpoch
    /\ mem_job \in [Job -> NullMemJob]

    /\ pc \in PC
    /\ local_job \in NullJob
    /\ local_version \in NullVersion

    /\ job_pc \in [Job -> {"Init", "Running", "ClearInMemJob", "Terminated"}]

    /\ background_pc \in {"Init", "UpdateToScheduled"}
    /\ background_job \in NullJob

    /\ num_rerun \in 0..max_rerun

Init ==
    /\ db_config = 10
    /\ db_epoch = 20
    /\ db_job = [j \in Job |-> nil]

    /\ mem_epoch = nil
    /\ mem_job = [j \in Job |-> nil]

    /\ pc = "Init"
    /\ local_job = nil
    /\ local_version = nil

    /\ job_pc = [j \in Job |-> "Init"]

    /\ background_pc = "Init"
    /\ background_job = nil

    /\ num_rerun = 0

-------------------------------------------------------------

jobUnchanged ==
    /\ UNCHANGED <<mem_epoch, mem_job>>
    /\ UNCHANGED <<pc, local_job, local_version>>
    /\ UNCHANGED job_pc
    /\ UNCHANGED <<background_pc, background_job>>

StartJob(j) ==
    LET
        init_job == [
            status |-> "Ready",
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
            /\ UNCHANGED mem_job

        when_smaller ==
            /\ mem_epoch' = db_epoch
            /\ mem_job' = [j \in Job |-> nil] \* TODO
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

    /\ UNCHANGED local_job
    /\ UNCHANGED db_job
    /\ UNCHANGED job_pc
    /\ UNCHANGED local_version
    /\ mainUnchanged

--------------------------

mainNormalUnchanged ==
    /\ UNCHANGED mem_epoch
    /\ UNCHANGED db_epoch
    /\ mainUnchanged

--------------------------

getNextJobCond(j) ==
    /\ db_job[j] # nil
    /\ db_job[j].status = "Ready"
    /\ db_job[j].epoch < mem_epoch

GetNextJob(j) ==
    /\ pc = "GetNextJob"
    /\ getNextJobCond(j)

    /\ pc' = "ScheduleMemJob"
    /\ local_job' = j

    /\ UNCHANGED mem_job
    /\ UNCHANGED db_job
    /\ UNCHANGED job_pc
    /\ UNCHANGED local_version
    /\ mainNormalUnchanged

--------------------------

ScheduleMemJob ==
    LET
        j == local_job
        job == db_job[j]

        init_job == [
            config |-> job.config,
            version |-> job.version,
            need_schedule |-> nil,
            scheduling |-> FALSE
        ]

        base_job ==
            IF mem_job[j] # nil
                THEN [mem_job[j] EXCEPT !.version = job.version]
                ELSE init_job

        scheduling_job == [base_job EXCEPT
            !.need_schedule = FALSE,
            !.scheduling = TRUE
        ]
        when_scheduled ==
            /\ ~base_job.scheduling
            /\ pc' = "UpdateToScheduled"
            /\ mem_job' = [mem_job EXCEPT ![j] = scheduling_job]
            /\ UNCHANGED local_version

        pending_job == [base_job EXCEPT !.need_schedule = TRUE]
        when_ignore ==
            /\ pc' = "UpdateJobEpoch"
            /\ mem_job' = [mem_job EXCEPT ![j] = pending_job]
            /\ local_version' = job.version
    IN
    /\ pc = "ScheduleMemJob"
    /\ \/ when_scheduled
       \/ when_ignore

    /\ UNCHANGED local_job
    /\ UNCHANGED db_job
    /\ UNCHANGED job_pc
    /\ mainNormalUnchanged

--------------------------

UpdateToScheduled ==
    LET
        j == local_job
    IN
    /\ pc = "UpdateToScheduled"
    /\ pc' = "Init"

    /\ db_job' = [db_job EXCEPT ![j].status = "Scheduled"]
    /\ job_pc' = [job_pc EXCEPT ![j] = "Running"]
    /\ local_job' = nil

    /\ UNCHANGED local_version
    /\ UNCHANGED mem_job
    /\ mainNormalUnchanged

--------------------------

UpdateJobEpoch ==
    LET
        j == local_job

        allow_update ==
            /\ db_job[j].status = "Ready"
            /\ db_job[j].version = local_version
    IN
    /\ pc = "UpdateJobEpoch"
    /\ pc' = "Init"
    /\ IF allow_update
        THEN db_job' = [db_job EXCEPT ![j].epoch = mem_epoch]
        ELSE UNCHANGED db_job
    /\ local_job' = nil
    /\ local_version' = nil

    /\ UNCHANGED mem_job
    /\ UNCHANGED job_pc
    /\ mainNormalUnchanged

-------------------------------------------------------------

runUnchanged ==
    /\ UNCHANGED <<pc, local_job, local_version>>
    /\ UNCHANGED db_config
    /\ UNCHANGED db_epoch
    /\ UNCHANGED mem_epoch
    /\ UNCHANGED <<background_pc, background_job>>
    /\ UNCHANGED num_rerun

FinishScheduledJob(j) ==
    LET
        update_to_finished ==
            db_job' = [db_job EXCEPT
                ![j].status = "Finished",
                ![j].epoch = 0
            ]
    IN
    /\ job_pc[j] = "Running"
    /\ job_pc' = [job_pc EXCEPT ![j] = "ClearInMemJob"]
    /\ IF db_job[j].status = "Scheduled"
        THEN update_to_finished
        ELSE UNCHANGED db_job

    /\ UNCHANGED mem_job
    /\ runUnchanged

--------------------------

ClearInMemJob(j) ==
    /\ job_pc[j] = "ClearInMemJob"
    /\ job_pc' = [job_pc EXCEPT ![j] = "Terminated"]
    /\ IF mem_job[j] = nil THEN
            UNCHANGED mem_job
        ELSE IF ~mem_job[j].need_schedule THEN
            mem_job' = [mem_job EXCEPT ![j] = nil]
        ELSE
            mem_job' = [mem_job EXCEPT ![j].scheduling = FALSE]
    /\ UNCHANGED db_job
    /\ runUnchanged

-------------------------------------------------------------

backgroundUnchanged ==
    /\ UNCHANGED <<pc, local_job, local_version>>
    /\ UNCHANGED mem_epoch
    /\ UNCHANGED db_config
    /\ UNCHANGED db_epoch
    /\ UNCHANGED num_rerun

BackgroundSchedule(j) ==
    /\ background_pc = "Init"
    /\ mem_job[j] # nil
    /\ mem_job[j].need_schedule
    /\ ~mem_job[j].scheduling

    /\ background_pc' = "UpdateToScheduled"
    /\ background_job' = j
    /\ mem_job' = [mem_job EXCEPT
            ![j].need_schedule = FALSE,
            ![j].scheduling = TRUE
        ]

    /\ UNCHANGED db_job
    /\ UNCHANGED job_pc
    /\ backgroundUnchanged

--------------------------

BackgroundUpdateToScheduled ==
    LET
        j == background_job
    IN
    /\ background_pc = "UpdateToScheduled"
    /\ background_pc' = "Init"
    /\ db_job' = [db_job EXCEPT ![j].status = "Scheduled"]
    /\ job_pc' = [job_pc EXCEPT ![j] = "Running"]
    /\ background_job' = nil

    /\ UNCHANGED mem_job
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

    /\ UNCHANGED <<pc, local_job, local_version>>
    /\ UNCHANGED <<background_pc, background_job>>
    /\ UNCHANGED num_rerun
    /\ UNCHANGED <<mem_epoch, mem_job>>
    /\ UNCHANGED job_pc

-------------------------------------------------------------

TerminateCond ==
    /\ pc = "GetNextJob"
    /\ \A j \in Job:
        /\ db_job[j] # nil
        /\ db_job[j].status = "Finished"
        /\ job_pc[j] = "Terminated"
    /\ background_pc = "Init"
    /\ mem_epoch = db_epoch

Terminated ==
    /\ TerminateCond
    /\ UNCHANGED vars

--------------------------

Next ==
    \/ \E j \in Job:
        \/ StartJob(j)
        \/ ReRunJob(j)
        \/ GetNextJob(j)
        \/ FinishScheduledJob(j)
        \/ ClearInMemJob(j)
        \/ BackgroundSchedule(j)
    \/ LoadConfig
    \/ ScheduleMemJob
    \/ UpdateToScheduled
    \/ UpdateJobEpoch

    \/ BackgroundUpdateToScheduled
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


DBJobStep ==
    LET
        start_step(j) ==
            /\ db_job[j] = nil
            /\ db_job'[j] # nil
            /\ db_job'[j].status = "Ready"

        schedule_step(j) ==
            /\ db_job[j] # nil
            /\ db_job[j].status = "Ready"
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

DBJobProperty ==
    [][DBJobStep]_db_job

====

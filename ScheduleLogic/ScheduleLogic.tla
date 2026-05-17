---- MODULE ScheduleLogic ----
EXTENDS TLC, Naturals

CONSTANTS Job, nil

VARIABLES
    db_config, db_epoch, mem_epoch,
    db_job, mem_job,
    pc, local_job,
    job_pc,
    background_pc, background_job

vars == <<
    db_config, db_epoch, mem_epoch,
    db_job, mem_job,
    pc, local_job,
    job_pc,
    background_pc, background_job
>>

-------------------------------------------------------------

Config == 10..19

Epoch == 21..29
NullEpoch == Epoch \union {nil}
ZeroEpoch == Epoch \union {0}

Status == {"Ready", "Scheduled", "Finished"}

NullJob == Job \union {nil}

DBJob == [
    status: Status,
    config: Config,
    epoch: ZeroEpoch
]
NullDBJob == DBJob \union {nil}

MemJob == [
    config: Config,
    status: {"Ready", "BeforeSchedule"},
    is_running: BOOLEAN
]
NullMemJob == MemJob \union {nil}

PC == {
    "Init", "GetNextJob",
    "ScheduleMemJob",
    "UpdateToScheduled", "UpdateMemScheduled",
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

    /\ job_pc \in [Job -> {"Init", "Running", "ClearInMemJob", "Terminated"}]

    /\ background_pc \in {"Init", "UpdateToScheduled", "UpdateMemScheduled"}
    /\ background_job \in NullJob

Init ==
    /\ db_config = 10
    /\ db_epoch = 20
    /\ db_job = [j \in Job |-> nil]

    /\ mem_epoch = nil
    /\ mem_job = [j \in Job |-> nil]

    /\ pc = "Init"
    /\ local_job = nil

    /\ job_pc = [j \in Job |-> "Init"]

    /\ background_pc = "Init"
    /\ background_job = nil

-------------------------------------------------------------

jobUnchanged ==
    /\ UNCHANGED <<mem_epoch, mem_job>>
    /\ UNCHANGED <<pc, local_job>>
    /\ UNCHANGED job_pc
    /\ UNCHANGED <<background_pc, background_job>>

StartJob(j) ==
    LET
        init_job == [
            status |-> "Ready",
            config |-> db_config,
            epoch |-> 0
        ]
    IN
    /\ db_job[j] = nil
    /\ db_job' = [db_job EXCEPT ![j] = init_job]
    /\ UNCHANGED db_config
    /\ UNCHANGED db_epoch
    /\ jobUnchanged

--------------------------

ReRunJob(j) ==
    /\ db_job[j] # nil
    /\ db_job[j].status # "Ready"
    /\ db_job' = [db_job EXCEPT
            ![j].status = "Ready",
            ![j].epoch = 0
        ]
    /\ UNCHANGED db_config
    /\ UNCHANGED db_epoch
    /\ jobUnchanged

-------------------------------------------------------------

mainUnchanged ==
    /\ UNCHANGED db_config
    /\ UNCHANGED <<background_pc, background_job>>

--------------------------

LoadConfig ==
    LET
        when_start ==
            /\ db_epoch' = db_epoch + 1
            /\ mem_epoch' = db_epoch'
            /\ UNCHANGED mem_job

        when_normal ==
            /\ UNCHANGED mem_job
            /\ UNCHANGED mem_epoch
            /\ UNCHANGED db_epoch
    IN
    /\ pc = "Init"
    /\ pc' = "GetNextJob"
    /\ IF mem_epoch = nil
        THEN when_start
        ELSE when_normal

    /\ UNCHANGED local_job
    /\ UNCHANGED mem_job
    /\ UNCHANGED db_job
    /\ UNCHANGED job_pc
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
    /\ mainNormalUnchanged

--------------------------

ScheduleMemJob ==
    LET
        j == local_job
        job == db_job[j]

        scheduling_job == [
            config |-> job.config,
            status |-> "BeforeSchedule",
            is_running |-> FALSE
        ]

        when_scheduled ==
            /\ pc' = "UpdateToScheduled"
            /\ mem_job' = [mem_job EXCEPT ![j] = scheduling_job]

        ready_job == [
            config |-> job.config,
            status |-> "Ready",
            is_running |-> FALSE
        ]

        when_ignore ==
            /\ pc' = "UpdateJobEpoch"
            /\ mem_job' = [mem_job EXCEPT ![j] = ready_job]
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
    /\ pc' = "UpdateMemScheduled"

    /\ db_job' = [db_job EXCEPT ![j].status = "Scheduled"]

    /\ UNCHANGED local_job
    /\ UNCHANGED mem_job
    /\ UNCHANGED job_pc
    /\ mainNormalUnchanged

--------------------------

UpdateMemScheduled ==
    LET
        j == local_job
    IN
    /\ pc = "UpdateMemScheduled"
    /\ pc' = "Init"
    /\ mem_job' = [mem_job EXCEPT ![j].is_running = TRUE]
    /\ local_job' = nil
    /\ job_pc' = [job_pc EXCEPT ![j] = "Running"]

    /\ UNCHANGED db_job
    /\ mainNormalUnchanged

--------------------------

UpdateJobEpoch ==
    LET
        j == local_job
    IN
    /\ pc = "UpdateJobEpoch"
    /\ pc' = "Init"
    /\ IF db_job[j].status = "Ready"
        THEN db_job' = [db_job EXCEPT ![j].epoch = mem_epoch]
        ELSE UNCHANGED db_job
    /\ local_job' = nil
    /\ UNCHANGED mem_job
    /\ UNCHANGED job_pc
    /\ mainNormalUnchanged

-------------------------------------------------------------

runUnchanged ==
    /\ UNCHANGED <<pc, local_job>>
    /\ UNCHANGED db_config
    /\ UNCHANGED db_epoch
    /\ UNCHANGED mem_epoch
    /\ UNCHANGED <<background_pc, background_job>>

FinishScheduledJob(j) ==
    /\ job_pc[j] = "Running"
    /\ job_pc' = [job_pc EXCEPT ![j] = "ClearInMemJob"]
    \* TODO conditional update
    /\ db_job' = [db_job EXCEPT
            ![j].status = "Finished",
            ![j].epoch = 0
        ]
    /\ UNCHANGED mem_job
    /\ runUnchanged

--------------------------

ClearInMemJob(j) ==
    /\ job_pc[j] = "ClearInMemJob"
    /\ job_pc' = [job_pc EXCEPT ![j] = "Terminated"]
    /\ IF mem_job[j].status = "BeforeSchedule"
        THEN mem_job' = [mem_job EXCEPT ![j] = nil]
        ELSE UNCHANGED mem_job \* TODO clear boolean flag
    /\ UNCHANGED db_job
    /\ runUnchanged

-------------------------------------------------------------

backgroundUnchanged ==
    /\ UNCHANGED <<pc, local_job>>
    /\ UNCHANGED mem_epoch
    /\ UNCHANGED db_config
    /\ UNCHANGED db_epoch

BackgroundSchedule(j) ==
    /\ background_pc = "Init"
    /\ mem_job[j] # nil
    /\ mem_job[j].status = "Ready" \* TODO add running cond

    /\ background_pc' = "UpdateToScheduled"
    /\ background_job' = j
    /\ mem_job' = [mem_job EXCEPT ![j].status = "BeforeSchedule"]

    /\ UNCHANGED db_job
    /\ UNCHANGED job_pc
    /\ backgroundUnchanged

--------------------------

BackgroundUpdateToScheduled ==
    LET
        j == background_job
    IN
    /\ background_pc = "UpdateToScheduled"
    /\ background_pc' = "UpdateMemScheduled"
    /\ db_job' = [db_job EXCEPT ![j].status = "Scheduled"]

    /\ UNCHANGED background_job
    /\ UNCHANGED job_pc
    /\ UNCHANGED mem_job
    /\ backgroundUnchanged

--------------------------

BackgroundUpdateMemScheduled ==
    LET
        j == background_job
    IN
    /\ background_pc = "UpdateMemScheduled"

    /\ background_pc' = "Init"
    /\ background_job' = nil
    /\ job_pc' = [job_pc EXCEPT ![j] = "Running"]
    /\ mem_job' = [mem_job EXCEPT ![j].is_running = TRUE]

    /\ UNCHANGED db_job
    /\ backgroundUnchanged

-------------------------------------------------------------

TerminateCond ==
    /\ pc = "GetNextJob"
    /\ \A j \in Job:
        /\ db_job[j] # nil
        /\ db_job[j].status = "Finished"
        /\ job_pc[j] = "Terminated"
    /\ background_pc = "Init"

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
    \/ UpdateMemScheduled
    \/ UpdateJobEpoch

    \/ BackgroundUpdateToScheduled
    \/ BackgroundUpdateMemScheduled

    \/ Terminated

Spec == Init /\ [][Next]_vars

-------------------------------------------------------------

NotScanWhenAlreadyInMem ==
    \A j \in Job:
        (ENABLED GetNextJob(j)) =>
            \/ mem_job[j] = nil
            \/ /\ mem_job[j] # nil
               /\ mem_job[j].status # "Ready"


TerminateInv ==
    LET
        db_job_cond ==
            \A j \in Job:
                /\ db_job[j].status = "Finished"
                /\ db_job[j].epoch = 0
    IN
    TerminateCond =>
        /\ db_job_cond

====

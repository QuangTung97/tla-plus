---- MODULE ScheduleLogic ----
EXTENDS TLC, Naturals

CONSTANTS Job, nil

VARIABLES
    db_config, db_epoch, mem_epoch,
    db_job, mem_job,
    pc, local_job,
    job_pc

vars == <<
    db_config, db_epoch, mem_epoch,
    db_job, mem_job,
    pc, local_job,
    job_pc
>>

-------------------------------------------------------------

Config == 10..19

Epoch == 20..29
NullEpoch == Epoch \union {nil}

Status == {"Ready", "Scheduled", "Finished"}

NullJob == Job \union {nil}

DBJob == [
    status: Status,
    config: Config,
    epoch: Epoch
]
NullDBJob == DBJob \union {nil}

MemJob == [
    config: Config,
    status: {"Added", "Scheduled"}
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
    /\ db_epoch \in Epoch
    /\ db_job \in [Job -> NullDBJob]

    /\ mem_epoch \in NullEpoch
    /\ mem_job \in [Job -> NullMemJob]

    /\ pc \in PC
    /\ local_job \in NullJob

    /\ job_pc \in [Job -> {"Init", "Terminated"}]

Init ==
    /\ db_config = 10
    /\ db_epoch = 20
    /\ db_job = [j \in Job |-> nil]

    /\ mem_epoch = nil
    /\ mem_job = [j \in Job |-> nil]

    /\ pc = "Init"
    /\ local_job = nil

    /\ job_pc = [j \in Job |-> "Init"]

-------------------------------------------------------------

jobUnchanged ==
    /\ UNCHANGED <<mem_epoch, mem_job>>
    /\ UNCHANGED <<pc, local_job>>
    /\ UNCHANGED job_pc

StartJob(j) ==
    LET
        init_job == [
            status |-> "Ready",
            config |-> db_config,
            epoch |-> 20
        ]
    IN
    /\ db_job[j] = nil
    /\ db_job' = [db_job EXCEPT ![j] = init_job]
    /\ UNCHANGED db_config
    /\ UNCHANGED db_epoch
    /\ jobUnchanged

-------------------------------------------------------------

mainUnchanged ==
    /\ UNCHANGED db_config
    /\ UNCHANGED job_pc

\* TODO use
at_least_one_scheduled ==
    \E j \in Job: mem_job[j] # nil /\ mem_job[j].status = "Scheduled"

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
    /\ UNCHANGED mem_epoch
    /\ UNCHANGED db_config
    /\ UNCHANGED db_epoch
    /\ mainUnchanged

--------------------------

mainNormalUnchanged ==
    /\ UNCHANGED mem_epoch
    /\ UNCHANGED db_config
    /\ UNCHANGED db_epoch
    /\ mainUnchanged

--------------------------

ScheduleMemJob ==
    LET
        j == local_job
        job == db_job[j]
        init_job == [
            config |-> job.config,
            status |-> "Added"
        ]

        when_scheduled ==
            /\ pc' = "UpdateToScheduled"
    IN
    /\ pc = "ScheduleMemJob"
    /\ mem_job' = [mem_job EXCEPT ![j] = init_job]
    /\ \/ when_scheduled

    /\ UNCHANGED local_job
    /\ UNCHANGED db_job
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
    /\ mainNormalUnchanged

--------------------------

UpdateMemScheduled ==
    LET
        j == local_job
    IN
    /\ pc = "UpdateMemScheduled"
    /\ pc' = "Init"
    /\ mem_job' = [mem_job EXCEPT ![j].status = "Scheduled"]
    /\ local_job' = nil

    /\ UNCHANGED db_job
    /\ mainNormalUnchanged

--------------------------

\* TODO use
UpdateJobEpoch ==
    /\ pc = "UpdateJobEpoch"
    /\ mainUnchanged

-------------------------------------------------------------

runUnchanged ==
    /\ UNCHANGED <<pc, local_job>>
    /\ UNCHANGED db_config
    /\ UNCHANGED db_epoch
    /\ UNCHANGED mem_epoch

FinishScheduledJob(j) ==
    /\ job_pc[j] = "Running"
    /\ runUnchanged

-------------------------------------------------------------

TerminateCond ==
    /\ pc = "GetNextJob"
    /\ \A j \in Job:
        /\ db_job[j] # nil
        /\ db_job[j].status = "Finished"

Terminated ==
    /\ TerminateCond
    /\ UNCHANGED vars

--------------------------

Next ==
    \/ \E j \in Job:
        \/ StartJob(j)
        \/ GetNextJob(j)
        \/ FinishScheduledJob(j)
    \/ ScheduleMemJob
    \/ UpdateToScheduled
    \/ UpdateMemScheduled
    \/ LoadConfig
    \/ Terminated

Spec == Init /\ [][Next]_vars

-------------------------------------------------------------

NotScanWhenAlreadyInMem ==
    \A j \in Job:
        (ENABLED GetNextJob(j)) => mem_job[j] = nil

====

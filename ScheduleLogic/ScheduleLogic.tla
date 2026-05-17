---- MODULE ScheduleLogic ----
EXTENDS TLC, Naturals

CONSTANTS Job, nil

VARIABLES
    db_config, db_epoch, mem_epoch,
    db_job, mem_job, pc

vars == <<
    db_config, db_epoch, mem_epoch,
    db_job, mem_job, pc
>>

-------------------------------------------------------------

Config == 10..19

Epoch == 20..29
NullEpoch == Epoch \union {nil}

Status == {"Ready", "Scheduled", "Finished"}

DBJob == [
    status: Status,
    config: Config,
    epoch: NullEpoch
]
NullDBJob == DBJob \union {nil}

MemJob == [
    config: Config,
    status: {"Ready", "Scheduled"}
]
NullMemJob == MemJob \union {nil}

PC == {"Init", "GetNextJob", "ScheduleJob"}

-------------------------------------------------------------

TypeOK ==
    /\ db_config \in Config
    /\ db_epoch \in Epoch
    /\ mem_epoch \in NullEpoch
    /\ db_job \in [Job -> NullDBJob]
    /\ mem_job \in [Job -> NullMemJob]
    /\ pc \in PC

Init ==
    /\ db_config = 10
    /\ db_epoch = 20
    /\ mem_epoch = nil
    /\ db_job = [j \in Job |-> nil]
    /\ mem_job = [j \in Job |-> nil]
    /\ pc = "Init"

-------------------------------------------------------------

jobUnchanged ==
    /\ UNCHANGED pc
    /\ UNCHANGED mem_epoch
    /\ UNCHANGED mem_job

StartJob(j) ==
    LET
        init_job == [
            status |-> "Ready",
            config |-> db_config,
            epoch |-> nil
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

    /\ UNCHANGED mem_job
    /\ UNCHANGED db_job
    /\ mainUnchanged

--------------------------

getNextJobCond(j) ==
    /\ db_job[j] # nil
    /\ db_job[j].status = "Ready"

GetNextJob(j) ==
    LET
        job == db_job[j]
        init_job == [
            config |-> job.config,
            status |-> "Ready"
        ]
    IN
    /\ pc = "GetNextJob"
    /\ getNextJobCond(j)

    /\ pc' = "ScheduleJob"
    /\ mem_job' = [mem_job EXCEPT ![j] = init_job]

    /\ UNCHANGED db_job
    /\ UNCHANGED mem_epoch
    /\ UNCHANGED db_config
    /\ UNCHANGED db_epoch
    /\ mainUnchanged

--------------------------

ScheduleJob(j) ==
    LET
        when_scheduled ==
            /\ mem_job' = [mem_job EXCEPT ![j].status = "Scheduled"]
            /\ db_job' = [db_job EXCEPT ![j].status = "Scheduled"]

        when_skip ==
            /\ UNCHANGED db_job
            /\ UNCHANGED mem_job
    IN
    /\ pc = "ScheduleJob"
    /\ mem_job[j] # nil
    /\ mem_job[j].status = "Ready"
    /\ pc' = "Init"
    /\ \/ when_scheduled
       \/ when_skip

    /\ UNCHANGED mem_epoch
    /\ UNCHANGED db_epoch
    /\ UNCHANGED db_config
    /\ mainUnchanged

-------------------------------------------------------------

TerminateCond ==
    /\ pc = "GetNextJob"

Terminated ==
    /\ TerminateCond
    /\ UNCHANGED vars

--------------------------

Next ==
    \/ \E j \in Job:
        \/ StartJob(j)
        \/ GetNextJob(j)
        \/ ScheduleJob(j)
    \/ LoadConfig
    \/ Terminated

Spec == Init /\ [][Next]_vars

-------------------------------------------------------------

NotScanWhenAlreadyInMem ==
    \A j \in Job:
        (ENABLED GetNextJob(j)) => mem_job[j] = nil

====

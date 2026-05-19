---- MODULE ScheduleLogic ----
EXTENDS TLC, Naturals

CONSTANTS
    Job, nil,
    max_rerun, max_db_config,
    max_failure, max_restart

VARIABLES
    db_config, db_epoch, mem_epoch,
    db_job, mem_job, scheduling_set, running_set,
    pc, local_job, local_version, local_epoch, local_scheduling_set,
    job_pc,
    background_pc,
    num_rerun, num_failure, num_restart

vars == <<
    db_config, db_epoch, mem_epoch,
    db_job, mem_job, scheduling_set, running_set,
    pc, local_job, local_version, local_epoch, local_scheduling_set,
    job_pc,
    background_pc,
    num_rerun, num_failure, num_restart
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
    version: JobVersion
]
NullMemJob == MemJob \union {nil}

PC == {
    "Init", "GetNextJob",
    "ScheduleMemJob",
    "UpdateJobEpoch"
}

BackgroundPC == {
    "Init",
    "UpdateToScheduled",
    "UpdateRunningSet"
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
    /\ local_scheduling_set \subseteq Job

    /\ job_pc \in [Job -> {"Init", "Running", "Terminated"}]

    /\ background_pc \in [Job -> BackgroundPC]

    /\ num_rerun \in 0..max_rerun
    /\ num_failure \in 0..max_failure
    /\ num_restart \in 0..max_restart

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
    /\ local_scheduling_set = {}

    /\ job_pc = [j \in Job |-> "Init"]

    /\ background_pc = [j \in Job |-> "Init"]

    /\ num_rerun = 0
    /\ num_failure = 0
    /\ num_restart = 0

-------------------------------------------------------------

localVarUnchanged ==
    /\ UNCHANGED <<pc, local_job>>
    /\ UNCHANGED <<local_version, local_epoch, local_scheduling_set>>

jobUnchanged ==
    /\ UNCHANGED <<mem_epoch, mem_job, scheduling_set, running_set>>
    /\ localVarUnchanged
    /\ UNCHANGED job_pc
    /\ UNCHANGED background_pc
    /\ UNCHANGED <<num_failure, num_restart>>

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
    /\ UNCHANGED <<num_rerun, num_restart>>

--------------------------

db_running_set ==
    {j \in Job: db_job[j] # nil /\ db_job[j].is_running}

new_running_set ==
    db_running_set \ scheduling_set

--------------------------

LoadConfig ==
    LET
        when_start ==
            /\ db_epoch' = db_epoch + 1
            /\ mem_epoch' = db_epoch'
            /\ mem_job' = [j \in Job |-> nil]
            /\ running_set' = new_running_set

        when_smaller ==
            /\ mem_epoch' = db_epoch
            /\ mem_job' = [j \in Job |-> nil]
            /\ UNCHANGED db_epoch
            /\ UNCHANGED running_set

        when_normal ==
            /\ UNCHANGED mem_job
            /\ UNCHANGED mem_epoch
            /\ UNCHANGED db_epoch
            /\ UNCHANGED running_set
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
    /\ local_scheduling_set' = scheduling_set

    /\ UNCHANGED scheduling_set
    /\ UNCHANGED background_pc
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
    /\ j \notin local_scheduling_set

GetNextJob(j) ==
    /\ pc = "GetNextJob"
    /\ getNextJobCond(j)

    /\ pc' = "ScheduleMemJob"
    /\ local_job' = j

    /\ UNCHANGED <<scheduling_set, running_set>>
    /\ UNCHANGED <<local_version, local_epoch, local_scheduling_set>>
    /\ UNCHANGED mem_job
    /\ UNCHANGED db_job
    /\ UNCHANGED background_pc
    /\ UNCHANGED job_pc
    /\ mainNormalUnchanged

GetNextJobReloadConfig ==
    /\ pc = "GetNextJob"
    /\ \/ mem_epoch # db_epoch
       \/ local_scheduling_set # scheduling_set
    /\ pc' = "Init"

    /\ UNCHANGED <<local_version, local_epoch, local_scheduling_set>>
    /\ UNCHANGED <<scheduling_set, running_set>>
    /\ UNCHANGED mem_job
    /\ UNCHANGED local_job
    /\ UNCHANGED db_job
    /\ UNCHANGED background_pc
    /\ UNCHANGED job_pc
    /\ mainNormalUnchanged

--------------------------

is_scheduling_or_running(j) ==
    \/ j \in scheduling_set
    \/ j \in running_set

background_goto(j, l) ==
    background_pc' = [background_pc EXCEPT ![j] = l]

ScheduleMemJob ==
    LET
        j == local_job
        job == db_job[j]

        when_scheduled ==
            /\ ~is_scheduling_or_running(j)
            /\ pc' = "Init"
            /\ scheduling_set' = scheduling_set \union {j}
            /\ mem_job' = [mem_job EXCEPT ![j] = nil]
            /\ background_goto(j, "UpdateToScheduled")
            /\ UNCHANGED local_version

        init_job == [
            config |-> job.config,
            version |-> job.version
        ]

        new_mem_job ==
            IF mem_job[j] # nil
                THEN [mem_job[j] EXCEPT !.version = job.version]
                ELSE init_job

        when_delayed ==
            /\ pc' = "UpdateJobEpoch"
            /\ mem_job' = [mem_job EXCEPT ![j] = new_mem_job]
            /\ local_version' = job.version
            /\ UNCHANGED background_pc
            /\ UNCHANGED scheduling_set
    IN
    /\ pc = "ScheduleMemJob"
    /\ \/ when_scheduled
       \/ when_delayed

    /\ UNCHANGED <<local_job, local_epoch, local_scheduling_set>>
    /\ UNCHANGED db_job
    /\ UNCHANGED job_pc
    /\ UNCHANGED running_set
    /\ mainNormalUnchanged

--------------------------

update_job_scheduled_and_start_success(j) ==
    /\ IF db_job[j].status = "Ready" THEN
            /\ db_job' = [db_job EXCEPT
                    ![j].status = "Scheduled",
                    ![j].epoch = 0,
                    ![j].is_running = TRUE
                ]
            /\ job_pc' = [job_pc EXCEPT ![j] = "Running"]
        ELSE
            /\ UNCHANGED db_job
            /\ UNCHANGED job_pc
    /\ UNCHANGED mem_epoch
    /\ UNCHANGED num_failure

update_job_scheduled_and_start_failed ==
    /\ num_failure < max_failure
    /\ num_failure' = num_failure + 1
    /\ mem_epoch' = nil
    /\ UNCHANGED db_job
    /\ UNCHANGED job_pc

update_job_scheduled_and_start(j) ==
    /\ \/ update_job_scheduled_and_start_success(j)
       \/ update_job_scheduled_and_start_failed
    /\ UNCHANGED mem_job
    /\ UNCHANGED <<scheduling_set, running_set>>

--------------------------

clear_local_vars ==
    /\ local_job' = nil
    /\ local_version' = nil
    /\ local_epoch' = nil
    /\ local_scheduling_set' = {}

do_update_running_set(j) ==
    /\ scheduling_set' = scheduling_set \ {j}
    /\ running_set' = running_set \union {j}
    /\ UNCHANGED mem_job
    /\ UNCHANGED job_pc
    /\ UNCHANGED db_job

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
        THEN db_job' = [db_job EXCEPT ![j].epoch = local_epoch]
        ELSE UNCHANGED db_job
    /\ clear_local_vars

    /\ UNCHANGED mem_job
    /\ UNCHANGED job_pc
    /\ UNCHANGED <<scheduling_set, running_set>>
    /\ UNCHANGED background_pc
    /\ mainNormalUnchanged

-------------------------------------------------------------

runUnchanged ==
    /\ localVarUnchanged
    /\ UNCHANGED db_config
    /\ UNCHANGED db_epoch
    /\ UNCHANGED mem_epoch
    /\ UNCHANGED background_pc
    /\ UNCHANGED <<scheduling_set, running_set>>
    /\ UNCHANGED <<num_rerun, num_failure, num_restart>>

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
    /\ localVarUnchanged
    /\ UNCHANGED db_config
    /\ UNCHANGED db_epoch
    /\ UNCHANGED <<num_rerun, num_restart>>

BackgroundSchedule(j) ==
    /\ background_pc[j] = "Init"
    /\ mem_job[j] # nil
    /\ ~is_scheduling_or_running(j)

    /\ background_goto(j, "UpdateToScheduled")
    /\ mem_job' = [mem_job EXCEPT ![j] = nil]
    /\ scheduling_set' = scheduling_set \union {j}

    /\ UNCHANGED db_job
    /\ UNCHANGED job_pc
    /\ UNCHANGED num_failure
    /\ UNCHANGED <<mem_epoch, running_set>>
    /\ backgroundUnchanged

--------------------------

BackgroundUpdateToScheduled(j) ==
    /\ background_pc[j]= "UpdateToScheduled"
    /\ background_goto(j, "UpdateRunningSet")
    /\ update_job_scheduled_and_start(j)

    /\ backgroundUnchanged

--------------------------

BackgroundUpdateRunningSet(j) ==
    /\ background_pc[j] = "UpdateRunningSet"
    /\ background_goto(j, "Init")

    /\ do_update_running_set(j)

    /\ UNCHANGED mem_epoch
    /\ UNCHANGED num_failure
    /\ backgroundUnchanged

-------------------------------------------------------------

BackgroundScanRunningSet ==
    /\ running_set # new_running_set
    /\ running_set' = new_running_set

    /\ UNCHANGED db_job
    /\ UNCHANGED mem_job
    /\ UNCHANGED scheduling_set
    /\ UNCHANGED job_pc
    /\ UNCHANGED background_pc
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

    /\ localVarUnchanged
    /\ UNCHANGED background_pc
    /\ UNCHANGED <<num_rerun, num_failure, num_restart>>
    /\ UNCHANGED <<mem_epoch, mem_job, scheduling_set, running_set>>
    /\ UNCHANGED job_pc

-------------------------------------------------------------

RestartSystem ==
    /\ num_restart < max_restart
    /\ num_restart' = num_restart + 1

    /\ mem_epoch' = nil
    /\ mem_job' = [j \in Job |-> nil]
    /\ scheduling_set' = {}
    /\ running_set' = {}
    /\ pc' = "Init"
    /\ clear_local_vars

    /\ background_pc' = [j \in Job |-> "Init"]

    /\ UNCHANGED <<db_config, db_job, db_epoch>>
    /\ UNCHANGED job_pc
    /\ UNCHANGED <<num_rerun, num_failure>>

-------------------------------------------------------------

TerminateCond ==
    /\ pc = "GetNextJob"
    /\ \A j \in Job:
        /\ db_job[j] # nil
        /\ db_job[j].status = "Finished"
        /\ ~db_job[j].is_running
        /\ job_pc[j] = "Terminated"
        /\ background_pc[j]= "Init"
        /\ mem_job[j] = nil
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
        \/ BackgroundUpdateToScheduled(j)
        \/ BackgroundUpdateRunningSet(j)
    \/ LoadConfig
    \/ GetNextJobReloadConfig
    \/ ScheduleMemJob
    \/ UpdateJobEpoch

    \/ BackgroundScanRunningSet

    \/ IncDBConfig
    \/ RestartSystem

    \/ Terminated

Spec == Init /\ [][Next]_vars

FairSpec == Spec /\ WF_vars(Next)

-------------------------------------------------------------

AlwaysTerminated == []<>TerminateCond

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
    LET
        pre_cond(j) ==
            /\ mem_epoch # nil
            /\ db_job[j] # nil
            /\ db_job[j].is_running
    IN
    \A j \in Job:
        pre_cond(j) => is_scheduling_or_running(j)

====

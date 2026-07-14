------ MODULE EdgeSync ----
EXTENDS TLC, Sequences, Naturals

CONSTANTS SyncJob, nil, max_log, max_retry

VARIABLES
    db_status, running, mem_log, db_log,
    next_log, num_retry

vars == <<
    db_status, running, mem_log, db_log,
    next_log, num_retry
>>

----------------------------------------------------------------------------

JobStatus == {"Init", "Ready", "Syncing", "Failed", "Success", "Gone"}

FinishStatus == {"Success", "Gone"}

ASSUME FinishStatus \subseteq JobStatus

LogEntry == 21..29

----------------------------------------------------------------------------

TypeOK ==
    /\ db_status \in [SyncJob -> JobStatus]
    /\ running \subseteq SyncJob
    /\ mem_log \in [SyncJob -> Seq(LogEntry)]
    /\ db_log \in [SyncJob -> Seq(LogEntry)]
    /\ next_log \in 20..29
    /\ num_retry \in 0..max_retry


Init ==
    /\ db_status = [j \in SyncJob |-> "Init"]
    /\ running = {}
    /\ mem_log = [j \in SyncJob |-> <<>>]
    /\ db_log = [j \in SyncJob |-> <<>>]
    /\ next_log = 20
    /\ num_retry = 0

----------------------------------------------------------------------------

MarkReady(j) ==
    /\ db_status[j] = "Init"
    /\ db_status' = [db_status EXCEPT ![j] = "Ready"]
    /\ UNCHANGED running
    /\ UNCHANGED <<mem_log, db_log, next_log>>
    /\ UNCHANGED num_retry


RetryJob(j) ==
    /\ db_status[j] # "Ready"
    /\ num_retry < max_retry
    /\ num_retry' = num_retry + 1
    /\ db_status' = [db_status EXCEPT ![j] = "Ready"]
    /\ UNCHANGED running
    /\ UNCHANGED <<mem_log, db_log, next_log>>


ScheduleSync(j) ==
    /\ db_status[j] = "Ready"
    /\ db_status' = [db_status EXCEPT ![j] = "Syncing"]
    /\ running' = running \union {j}
    /\ UNCHANGED <<mem_log, db_log, next_log>>
    /\ UNCHANGED num_retry


AppendLog(j) ==
    /\ j \in running
    /\ next_log < max_log
    /\ next_log' = next_log + 1
    /\ mem_log' = [mem_log EXCEPT ![j] = Append(@, next_log')]
    /\ UNCHANGED <<db_log, db_status>>
    /\ UNCHANGED running
    /\ UNCHANGED num_retry


JobCompleted(j) ==
    /\ j \in running
    /\ running' = running \ {j}
    /\ db_log' = [db_log EXCEPT ![j] = mem_log[j]]
    /\ db_status' = [db_status EXCEPT ![j] = "Success"]
    /\ UNCHANGED mem_log
    /\ UNCHANGED next_log
    /\ UNCHANGED num_retry


SystemRestart ==
    LET
        clear_log(j) ==
            IF j \in running
                THEN <<>>
                ELSE mem_log[j]
    IN
    /\ running # {}
    /\ running' = {}
    /\ mem_log' = [j \in SyncJob |-> clear_log(j)]
    /\ UNCHANGED next_log
    /\ UNCHANGED db_log
    /\ UNCHANGED db_status
    /\ UNCHANGED num_retry


ClearGoneJob(j) ==
    /\ db_status[j] = "Syncing"
    /\ j \notin running
    /\ db_status' = [db_status EXCEPT ![j] = "Gone"]
    /\ db_log' = [db_log EXCEPT ![j] = <<>>]
    /\ UNCHANGED <<mem_log, running>>
    /\ UNCHANGED next_log
    /\ UNCHANGED num_retry

----------------------------------------------------------------------------

TerminateCond ==
    /\ \A j \in SyncJob: db_status[j] \in {"Success", "Gone"}

Terminated ==
    /\ TerminateCond
    /\ UNCHANGED vars


Next ==
    \/ \E j \in SyncJob:
        \/ MarkReady(j)
        \/ RetryJob(j)
        \/ ScheduleSync(j)
        \/ AppendLog(j)
        \/ JobCompleted(j)
        \/ ClearGoneJob(j)
    \/ SystemRestart
    \/ Terminated


Spec == Init /\ [][Next]_vars

FairSpec == Spec /\ WF_vars(Next)

----------------------------------------------------------------------------

AlwaysTerminate == []<> TerminateCond


SyncJobStopInv ==
    \A j \in SyncJob:
        db_status[j] \in FinishStatus => db_log[j] = mem_log[j]


WhenTerminatedInv ==
    LET
        cond ==
            \A j \in SyncJob:
                /\ db_log[j] = mem_log[j]
    IN
    TerminateCond => cond

====

------ MODULE SyncJob ----
EXTENDS TLC, Naturals, Sequences

CONSTANTS SyncSlave, JobID, nil

VARIABLES db_jobs, db_hist, mem_jobs, pc, current_job,
    fill_pc, fill_job, slave_state

main_vars == <<pc, current_job>>

fill_vars == <<fill_pc, fill_job>>

vars == <<db_jobs, db_hist, mem_jobs, main_vars, fill_vars, slave_state>>


JobStatus == {"Ready", "Scheduled", "Succeeded", "Failed"}

Job == [id: JobID, status: JobStatus, handled: BOOLEAN]

NullJob == Job \union {nil}

JobHist == [job_id: JobID, status: {"Running", "Succeeded", "Failed"}]


TypeOK ==
    /\ db_jobs \in [JobID -> NullJob]
    /\ mem_jobs \in [JobID -> NullJob]
    /\ db_hist \in Seq(JobHist)

    /\ pc \in {"Init", "InsertHist", "UpdateJobMem", "PushJob"}
    /\ current_job \in NullJob

    /\ fill_pc \in {"Init", "FillSetToMem", "FillUpdateDB"}
    /\ fill_job \in NullJob

    /\ slave_state \in [SyncSlave -> Seq(JobHist)]


Init ==
    /\ db_jobs = [j \in JobID |-> nil]
    /\ mem_jobs = [j \in JobID |-> nil]
    /\ db_hist = <<>>
    /\ pc = "Init"
    /\ current_job = nil
    /\ fill_pc = "Init"
    /\ fill_job = nil
    /\ slave_state = [s \in SyncSlave |-> <<>>]


InsertNewJob(id) ==
    LET
        new_job == [id |-> id, status |-> "Ready", handled |-> FALSE]
    IN
        /\ db_jobs[id] = nil
        /\ db_jobs' = [db_jobs EXCEPT ![id] = new_job]
        /\ UNCHANGED mem_jobs
        /\ UNCHANGED fill_vars
        /\ UNCHANGED main_vars
        /\ UNCHANGED db_hist
        /\ UNCHANGED slave_state


FillLoadJob(id) ==
    /\ fill_pc = "Init"
    /\ fill_pc' = "FillSetToMem"

    /\ db_jobs[id] # nil
    /\ db_jobs[id].status = "Ready"
    /\ db_jobs[id].handled = FALSE

    /\ fill_job' = db_jobs[id]
    /\ UNCHANGED db_jobs
    /\ UNCHANGED mem_jobs
    /\ UNCHANGED main_vars
    /\ UNCHANGED db_hist
    /\ UNCHANGED slave_state


FillSetToMem ==
    /\ fill_pc = "FillSetToMem"
    /\ fill_pc' = "FillUpdateDB"
    /\ mem_jobs' = [mem_jobs EXCEPT ![fill_job.id] = fill_job]
    /\ UNCHANGED fill_job
    /\ UNCHANGED db_jobs
    /\ UNCHANGED main_vars
    /\ UNCHANGED db_hist
    /\ UNCHANGED slave_state


FillUpdateDB ==
    /\ fill_pc = "FillUpdateDB"
    /\ fill_pc' = "Init"
    /\ db_jobs' = [db_jobs EXCEPT ![fill_job.id].handled = TRUE]
    /\ UNCHANGED fill_job
    /\ UNCHANGED mem_jobs
    /\ UNCHANGED main_vars
    /\ UNCHANGED db_hist
    /\ UNCHANGED slave_state


GetReadyJobInMem(id) ==
    /\ mem_jobs[id] # nil
    /\ mem_jobs[id].status = "Ready"
    /\ pc = "Init"
    /\ pc' = "InsertHist"
    /\ current_job' = mem_jobs[id]
    /\ UNCHANGED mem_jobs
    /\ UNCHANGED db_jobs
    /\ UNCHANGED fill_vars
    /\ UNCHANGED db_hist
    /\ UNCHANGED slave_state


InsertJobHist ==
    LET
        id == current_job.id
    IN
        /\ pc = "InsertHist"
        /\ pc' = "UpdateJobMem"
        /\ db_hist' = Append(db_hist, [job_id |-> id, status |-> "Running"])
        /\ db_jobs' = [db_jobs EXCEPT ![id].status = "Scheduled"]
        /\ UNCHANGED current_job
        /\ UNCHANGED mem_jobs
        /\ UNCHANGED fill_vars
        /\ UNCHANGED slave_state


UpdateJobMem ==
    LET
        id == current_job.id
    IN
        /\ pc = "UpdateJobMem"
        /\ pc' = "PushJob"
        /\ mem_jobs' = [mem_jobs EXCEPT ![id].status = "Scheduled"]
        /\ UNCHANGED current_job
        /\ UNCHANGED db_hist
        /\ UNCHANGED db_jobs
        /\ UNCHANGED fill_vars
        /\ UNCHANGED slave_state


lastDBHist == db_hist[Len(db_hist)]

PushJob(s) ==
    /\ pc = "PushJob"
    /\ pc' = "Init"
    /\ slave_state' = [slave_state EXCEPT ![s] = Append(@, lastDBHist)]
    /\ UNCHANGED mem_jobs
    /\ UNCHANGED current_job
    /\ UNCHANGED db_hist
    /\ UNCHANGED db_jobs
    /\ UNCHANGED fill_vars


SlaveFinishJob(s) ==
    LET
        changeStatus(h) ==
            /\ slave_state' = [slave_state EXCEPT ![]]

        doFinishHist(h) ==
            /\ h.status = "Running"
            /\ UNCHANGED fill_vars
            /\ UNCHANGED main_vars
            /\ UNCHANGED db_hist
            /\ UNCHANGED db_jobs
    IN
    \E i \in DOMAIN slave_state[s]: doFinishHist(slave_state[s][i])


TerminateCond ==
    LET
        histStatusFinish(h) ==
            \/ h.status = "Failed"
            \/ h.status = "Succeeded"
        allHistFinished(s) ==
            \A i \in DOMAIN slave_state[s]: histStatusFinish(slave_state[s][i])
    IN
        /\ pc = "Init"
        /\ fill_pc = "Init"
        /\ \A s \in SyncSlave: allHistFinished(s)

Terminated ==
    /\ TerminateCond
    /\ UNCHANGED vars


Next ==
    \/ \E id \in JobID:
        \/ InsertNewJob(id)
        \/ FillLoadJob(id)

        \/ GetReadyJobInMem(id)
    \/ FillSetToMem
    \/ FillUpdateDB

    \/ InsertJobHist
    \/ UpdateJobMem

    \/ \E s \in SyncSlave:
        \/ PushJob(s)
        \/ SlaveFinishJob(s)

    \/ Terminated


Spec == Init /\ [][Next]_vars


====

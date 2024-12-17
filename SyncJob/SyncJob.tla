------ MODULE SyncJob ----
EXTENDS TLC, Naturals, Sequences, FiniteSets

CONSTANTS SyncSlave, JobID, nil

VARIABLES db_jobs, db_hist, mem_jobs, job_hist_map,
    pc, current_job, current_hist_id,
    fill_pc, fill_job, slave_state,
    hist_update_pc, hist_update_id, hist_update_job_id,
    num_update_job

main_vars == <<pc, current_job, current_hist_id, num_update_job>>

fill_vars == <<fill_pc, fill_job>>

hist_update_vars == <<hist_update_pc, hist_update_id, hist_update_job_id>>

vars == <<db_jobs, db_hist, mem_jobs, job_hist_map, main_vars,
    fill_vars, slave_state, hist_update_vars>>


NullJobID == JobID \union {nil}

JobStatus == {"Ready", "Scheduled", "Succeeded", "Failed"}

Job == [id: JobID, status: JobStatus, handled: BOOLEAN, version: Nat]

NullJob == Job \union {nil}

HistStatus == {"Running", "Succeeded", "Failed"}

JobHist == [id: DOMAIN db_hist, job_id: JobID, status: HistStatus]

max_update_job == 2

NullHistID == (DOMAIN db_hist) \union {nil}

TypeOK ==
    /\ db_jobs \in [JobID -> NullJob]
    /\ mem_jobs \in [JobID -> NullJob]
    /\ job_hist_map \in [JobID -> NullHistID]
    /\ db_hist \in Seq(JobHist)

    /\ pc \in {"Init", "InsertHist", "UpdateJobMem", "PushJob"}
    /\ current_job \in NullJob
    /\ current_hist_id \in NullHistID

    /\ fill_pc \in {"Init", "FillSetToMem", "FillUpdateDB"}
    /\ fill_job \in NullJob

    /\ slave_state \in [SyncSlave -> Seq(JobHist)]

    /\ hist_update_pc \in {"Init", "HistUpdateSetMemJob"}
    /\ hist_update_id \in NullHistID
    /\ hist_update_job_id \in NullJobID

    /\ num_update_job \in Nat


Init ==
    /\ db_jobs = [j \in JobID |-> nil]
    /\ mem_jobs = [j \in JobID |-> nil]
    /\ job_hist_map = [j \in JobID |-> nil]
    /\ db_hist = <<>>
    /\ pc = "Init"
    /\ current_job = nil
    /\ current_hist_id = nil
    /\ fill_pc = "Init"
    /\ fill_job = nil
    /\ slave_state = [s \in SyncSlave |-> <<>>]

    /\ hist_update_pc = "Init"
    /\ hist_update_id = nil
    /\ hist_update_job_id = nil

    /\ num_update_job = 0


InsertNewJob(id) ==
    LET
        new_job == [id |-> id, status |-> "Ready", handled |-> FALSE, version |-> 1]
    IN
        /\ db_jobs[id] = nil
        /\ db_jobs' = [db_jobs EXCEPT ![id] = new_job]
        /\ UNCHANGED job_hist_map
        /\ UNCHANGED mem_jobs
        /\ UNCHANGED fill_vars
        /\ UNCHANGED main_vars
        /\ UNCHANGED db_hist
        /\ UNCHANGED slave_state
        /\ UNCHANGED hist_update_vars


UpdateJob(id) ==
    /\ db_jobs[id] # nil

    /\ num_update_job < max_update_job
    /\ num_update_job' = num_update_job + 1

    /\ db_jobs[id].status # "Ready"
    /\ db_jobs' = [db_jobs EXCEPT ![id] = [@ EXCEPT
        !.status = "Ready", !.handled = FALSE, !.version = @ + 1]]

    /\ UNCHANGED db_hist
    /\ UNCHANGED slave_state
    /\ UNCHANGED fill_vars
    /\ UNCHANGED mem_jobs
    /\ UNCHANGED job_hist_map
    /\ UNCHANGED <<pc, current_job, current_hist_id>>
    /\ UNCHANGED hist_update_vars


FillLoadJob(id) ==
    /\ fill_pc = "Init"
    /\ fill_pc' = "FillSetToMem"

    /\ db_jobs[id] # nil
    /\ db_jobs[id].status = "Ready"
    /\ db_jobs[id].handled = FALSE

    /\ fill_job' = db_jobs[id]
    /\ UNCHANGED db_jobs
    /\ UNCHANGED mem_jobs
    /\ UNCHANGED job_hist_map
    /\ UNCHANGED main_vars
    /\ UNCHANGED db_hist
    /\ UNCHANGED slave_state
    /\ UNCHANGED hist_update_vars


FillSetToMem ==
    /\ fill_pc = "FillSetToMem"
    /\ fill_pc' = "FillUpdateDB"
    /\ mem_jobs' = [mem_jobs EXCEPT ![fill_job.id] = fill_job]
    /\ UNCHANGED job_hist_map
    /\ UNCHANGED fill_job
    /\ UNCHANGED db_jobs
    /\ UNCHANGED main_vars
    /\ UNCHANGED db_hist
    /\ UNCHANGED slave_state
    /\ UNCHANGED hist_update_vars


FillUpdateDB ==
    /\ fill_pc = "FillUpdateDB"
    /\ fill_pc' = "Init"
    /\ IF fill_job.version = db_jobs[fill_job.id].version
        THEN db_jobs' = [db_jobs EXCEPT ![fill_job.id].handled = TRUE]
        ELSE UNCHANGED db_jobs
    /\ UNCHANGED fill_job
    /\ UNCHANGED mem_jobs
    /\ UNCHANGED job_hist_map
    /\ UNCHANGED main_vars
    /\ UNCHANGED db_hist
    /\ UNCHANGED slave_state
    /\ UNCHANGED hist_update_vars


GetReadyJobInMem(id) ==
    /\ mem_jobs[id] # nil
    /\ mem_jobs[id].status = "Ready"
    /\ job_hist_map[id] = nil
    /\ pc = "Init"
    /\ pc' = "InsertHist"
    /\ mem_jobs' = [mem_jobs EXCEPT ![id].status = "Scheduled"]
    /\ current_job' = mem_jobs[id]
    /\ UNCHANGED current_hist_id
    /\ UNCHANGED num_update_job
    /\ UNCHANGED job_hist_map
    /\ UNCHANGED db_jobs
    /\ UNCHANGED fill_vars
    /\ UNCHANGED db_hist
    /\ UNCHANGED slave_state
    /\ UNCHANGED hist_update_vars


InsertJobHist ==
    LET
        job_id == current_job.id
        hist_id == Len(db_hist) + 1
        new_job_hist == [id |-> hist_id, job_id |-> job_id, status |-> "Running"]
    IN
        /\ pc = "InsertHist"
        /\ pc' = "UpdateJobMem"
        /\ db_hist' = Append(db_hist, new_job_hist)
        /\ db_jobs' = [db_jobs EXCEPT ![job_id].status = "Scheduled"]
        /\ current_hist_id' = hist_id
        /\ UNCHANGED current_job
        /\ UNCHANGED mem_jobs
        /\ UNCHANGED job_hist_map
        /\ UNCHANGED num_update_job
        /\ UNCHANGED fill_vars
        /\ UNCHANGED slave_state
        /\ UNCHANGED hist_update_vars


UpdateJobMem ==
    LET
        id == current_job.id
    IN
        /\ pc = "UpdateJobMem"
        /\ pc' = "PushJob"
        /\ job_hist_map' = [job_hist_map EXCEPT ![id] = current_hist_id]
        /\ current_hist_id' = nil
        /\ UNCHANGED mem_jobs
        /\ UNCHANGED num_update_job
        /\ UNCHANGED current_job
        /\ UNCHANGED db_hist
        /\ UNCHANGED db_jobs
        /\ UNCHANGED fill_vars
        /\ UNCHANGED slave_state
        /\ UNCHANGED hist_update_vars


lastDBHist == db_hist[Len(db_hist)]

PushJob(s) ==
    /\ pc = "PushJob"
    /\ pc' = "Init"
    /\ slave_state' = [slave_state EXCEPT ![s] = Append(@, lastDBHist)]
    /\ UNCHANGED num_update_job
    /\ UNCHANGED mem_jobs
    /\ UNCHANGED job_hist_map
    /\ UNCHANGED current_hist_id
    /\ UNCHANGED current_job
    /\ UNCHANGED db_hist
    /\ UNCHANGED db_jobs
    /\ UNCHANGED fill_vars
    /\ UNCHANGED hist_update_vars


SlaveFinishJob(s) ==
    LET
        changeStatus(h, i) ==
            \/ slave_state' = [slave_state EXCEPT ![s][i].status = "Succeeded"]
            \/ slave_state' = [slave_state EXCEPT ![s][i].status = "Failed"]

        doFinishHist(h, i) ==
            /\ h.status = "Running"
            /\ changeStatus(h, i)
            /\ UNCHANGED fill_vars
            /\ UNCHANGED main_vars
            /\ UNCHANGED db_hist
            /\ UNCHANGED db_jobs
            /\ UNCHANGED mem_jobs
            /\ UNCHANGED job_hist_map
            /\ UNCHANGED hist_update_vars
    IN
        \E i \in DOMAIN slave_state[s]: doFinishHist(slave_state[s][i], i)


UpdateDBJobHistStatus(s) ==
    LET
        updateDBJob(job_id, st) ==
            IF db_jobs[job_id].status = "Scheduled"
                THEN db_jobs' = [db_jobs EXCEPT ![job_id].status = st]
                ELSE UNCHANGED db_jobs

        doUpdateHistStatus(h, i) ==
            /\ hist_update_pc = "Init"
            /\ hist_update_pc' = "HistUpdateSetMemJob"

            /\ h.status = "Succeeded" \/ h.status = "Failed"
            /\ db_hist[h.id].status = "Running"

            /\ db_hist' = [db_hist EXCEPT ![h.id].status = h.status]
            /\ updateDBJob(h.job_id, h.status)
            /\ hist_update_job_id' = h.job_id
            /\ hist_update_id' = h.id

            /\ UNCHANGED slave_state
            /\ UNCHANGED mem_jobs
            /\ UNCHANGED job_hist_map
            /\ UNCHANGED fill_vars
            /\ UNCHANGED main_vars
    IN
        \E i \in DOMAIN slave_state[s]: doUpdateHistStatus(slave_state[s][i], i)


HistUpdateSetMemJob ==
    LET 
        clear_cond ==
            /\ hist_update_id = job_hist_map[hist_update_job_id]

        delete_mem_job_cond ==
            /\ hist_update_id = job_hist_map[hist_update_job_id]
            /\ mem_jobs[hist_update_job_id].status = "Scheduled"

        clear_job_hist_map ==
            job_hist_map' = [job_hist_map EXCEPT ![hist_update_job_id] = nil]
    IN
        /\ hist_update_pc = "HistUpdateSetMemJob"
        /\ hist_update_pc' = "Init"
        /\ IF delete_mem_job_cond
            THEN
                /\ mem_jobs' = [mem_jobs EXCEPT ![hist_update_job_id] = nil]
            ELSE
                /\ UNCHANGED mem_jobs
        /\ clear_job_hist_map
        /\ hist_update_job_id' = nil
        /\ hist_update_id' = nil
        /\ UNCHANGED slave_state
        /\ UNCHANGED db_hist
        /\ UNCHANGED db_jobs
        /\ UNCHANGED fill_vars
        /\ UNCHANGED main_vars


TerminateCond ==
    LET
        histStatusFinish(h) ==
            \/ h.status = "Failed"
            \/ h.status = "Succeeded"

        allSlaveHistFinished(s) ==
            \A i \in DOMAIN slave_state[s]: histStatusFinish(slave_state[s][i])
        
        jobFinished(id) ==
            \/ db_jobs[id].status = "Succeeded"
            \/ db_jobs[id].status = "Failed"
    IN
        /\ pc = "Init"
        /\ fill_pc = "Init"
        /\ hist_update_pc = "Init"
        /\ \A s \in SyncSlave: allSlaveHistFinished(s)
        /\ \A i \in DOMAIN db_hist: histStatusFinish(db_hist[i])
        /\ \A id \in JobID: db_jobs[id] # nil /\ jobFinished(id)
        /\ num_update_job = max_update_job

Terminated ==
    /\ TerminateCond
    /\ UNCHANGED vars


Next ==
    \/ \E id \in JobID:
        \/ InsertNewJob(id)
        \/ UpdateJob(id)
        \/ FillLoadJob(id)

        \/ GetReadyJobInMem(id)
    \/ FillSetToMem
    \/ FillUpdateDB

    \/ InsertJobHist
    \/ UpdateJobMem

    \/ \E s \in SyncSlave:
        \/ PushJob(s)
        \/ SlaveFinishJob(s)
        \/ UpdateDBJobHistStatus(s)

    \/ HistUpdateSetMemJob

    \/ Terminated


Spec == Init /\ [][Next]_vars


JobHistNotRunConcurrently ==
    LET
        histSetOfJob(id) ==
            {i \in DOMAIN db_hist:
                /\ db_hist[i].job_id = id
                /\ db_hist[i].status = "Running"}

        numHistOfJob(id) == Cardinality(histSetOfJob(id))
    IN
        \A id \in JobID: numHistOfJob(id) <= 1

                
TerminateShouldCreateEnoughHist ==
    LET
        createdEnoughHist == Len(db_hist) = Cardinality(JobID) + max_update_job
    IN
        TerminateCond => createdEnoughHist


Sym == Permutations(JobID) \union Permutations(SyncSlave)


====

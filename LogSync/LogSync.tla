-- ---- MODULE LogSync ----
EXTENDS TLC, Naturals, Sequences

CONSTANTS Key, WatchClient, nil

\* state is in-memory data
\* db is the same data but on the db
\* watch_chan is the receive channel for client
VARIABLES pc, current_key, db, 
    state, state_seq, next_log, next_seq, watch_list,
    watch_pc, watch_keys, watch_chan, watch_seq,
    watch_log_index, watch_state, watch_local_key

main_vars == <<pc, current_key, db>>

watch_vars == <<watch_pc, watch_keys, watch_chan,
    watch_seq, watch_log_index, watch_state, watch_local_key>>

server_vars == <<state, state_seq, next_log, next_seq, watch_list>>

vars == <<main_vars, server_vars, watch_vars>>


max_log_size == 2

Status == {"Running", "Completed", "Gone"}

LogEntry == 20..30

SeqMaxLen(S, n) == UNION {[1..m -> S] : m \in 0..n}

Info == [logs: Seq(LogEntry), status: Status]

NullInfo == Info \union {nil}

NullKey == Key \union {nil}

NullLogEntry == LogEntry \union {nil}

Event == [
    type: {"AddLog", "Finished"},
    key: Key, line: NullLogEntry]

NullEvent == Event \union {nil}

Channel == [status: {"Empty", "Ready", "Consumed"}, data: NullEvent]

StateSeq == 100..120

WatchState == {"Init", "AddToWaitList", "WaitOnChan", "UpdateDB"}

TypeOK ==
    /\ pc \in {"Init", "PushJob"}
    /\ current_key \in NullKey
    /\ db \in [Key -> NullInfo]

    /\ state \in [Key -> NullInfo]
    /\ state_seq \in [Key -> StateSeq]
    /\ next_log \in LogEntry
    /\ next_seq \in StateSeq
    /\ watch_list \in [Key -> SUBSET WatchClient]

    /\ watch_pc \in [WatchClient -> WatchState]
    /\ watch_keys \in [WatchClient -> SUBSET Key]
    /\ watch_chan \in [WatchClient -> Channel]
    /\ watch_seq \in [WatchClient -> [Key -> StateSeq]]
    /\ watch_log_index \in [WatchClient -> [Key -> Nat]]
    /\ watch_state \in [WatchClient -> [Key -> NullInfo]]
    /\ watch_local_key \in [WatchClient -> NullKey]


consumed_chan == [status |-> "Consumed", data |-> nil]

Init ==
    /\ pc = "Init"
    /\ current_key = nil
    /\ db = [k \in Key |-> nil]

    /\ state = [k \in Key |-> nil]
    /\ state_seq = [k \in Key |-> 100]
    /\ next_log = 20
    /\ watch_list = [k \in Key |-> {}]
    /\ next_seq = 100

    /\ watch_pc = [c \in WatchClient |-> "Init"]
    /\ watch_keys = [c \in WatchClient |-> {}]
    /\ watch_chan = [c \in WatchClient |-> consumed_chan]
    /\ watch_seq = [c \in WatchClient |-> [k \in Key|-> 100]]
    /\ watch_log_index = [c \in WatchClient |-> [k \in Key |-> 0]]
    /\ watch_state = [c \in WatchClient |-> [k \in Key |-> nil]]
    /\ watch_local_key = [c \in WatchClient |-> nil]


newJob == [logs |-> <<>>, status |-> "Running"]


AddDBJob(k) ==
    /\ pc = "Init"
    /\ state[k] = nil
    /\ pc' = "PushJob"
    /\ current_key' = k
    /\ db' = [db EXCEPT ![k] = newJob]
    /\ UNCHANGED server_vars
    /\ UNCHANGED watch_vars


updateStateSeq(k) ==
    /\ next_seq' = next_seq + 1
    /\ state_seq' = [state_seq EXCEPT ![k] = next_seq']


PushJob ==
    /\ pc = "PushJob"
    /\ pc' = "Init"
    /\ current_key' = nil
    /\ state' = [state EXCEPT ![current_key] = db[current_key]]
    /\ UNCHANGED <<next_seq, state_seq>>
    /\ UNCHANGED watch_list
    /\ UNCHANGED db
    /\ UNCHANGED next_log
    /\ UNCHANGED watch_vars



canPushKeyToClient(k, c, old_watch_ch) ==
    /\ old_watch_ch[c].status = "Empty"
    /\ c \in watch_list'[k]
    /\ watch_seq[c][k] < state_seq'[k]

pushToClientChan(k, c, old_watch_ch) ==
    LET
        last_index == watch_log_index[c][k]
        state_index == Len(state'[k].logs)

        new_line == state'[k].logs[last_index + 1]

        add_event == [
            type |-> "AddLog",
            key |-> k,
            line |-> new_line]
        
        finish_event == [
            type |-> "Finished",
            key |-> k,
            line |-> nil]

        is_running == state'[k].status = "Running"

        add_log_cond == is_running \/ last_index < state_index

        update_seq_cond ==
            IF last_index = state_index
                THEN TRUE
                ELSE IF last_index + 1 = state_index /\ is_running
                    THEN TRUE
                    ELSE FALSE
        
        new_event ==
            IF add_log_cond
                THEN add_event
                ELSE finish_event
        
        new_state == [status |-> "Ready", data |-> new_event]
    IN
        /\ watch_chan' = [old_watch_ch EXCEPT ![c] = new_state]
        /\ watch_log_index' = [watch_log_index EXCEPT ![c][k] = last_index + 1]
        /\ IF update_seq_cond
            THEN watch_seq' = [watch_seq EXCEPT ![c][k] = state_seq'[k]]
            ELSE UNCHANGED watch_seq


pushToClientOrDoNothing(c, old_watch_ch) ==
    LET
        doNothing ==
            /\ \A k \in Key: ~canPushKeyToClient(k, c, old_watch_ch)
            /\ watch_chan' = old_watch_ch
            /\ UNCHANGED <<watch_seq, watch_log_index>>
    IN
    \/ \E k \in Key:
        /\ canPushKeyToClient(k, c, old_watch_ch)
        /\ pushToClientChan(k, c, old_watch_ch)
    \/ doNothing


pushKeyOrDoNothing(k) ==
    LET
        doPush ==
            \E c \in WatchClient:
                /\ canPushKeyToClient(k, c, watch_chan)
                /\ pushToClientChan(k, c, watch_chan)

        doNothing ==
            /\ \A c \in WatchClient: ~canPushKeyToClient(k, c, watch_chan)
            /\ UNCHANGED <<watch_chan, watch_seq, watch_log_index>>
    IN
        doPush \/ doNothing

ProduceLog(k) ==
    /\ state[k] # nil
    /\ state[k].status = "Running"
    /\ Len(state[k].logs) < max_log_size

    /\ next_log' = next_log + 1
    /\ state' = [state EXCEPT ![k].logs = Append(@, next_log')]

    /\ updateStateSeq(k)

    /\ UNCHANGED watch_list
    /\ pushKeyOrDoNothing(k)

    /\ UNCHANGED main_vars
    /\ UNCHANGED <<watch_pc, watch_keys, watch_state, watch_local_key>>


FinishJob(k) ==
    /\ state[k] # nil
    /\ state[k].status = "Running"
    /\ state' = [state EXCEPT ![k].status = "Completed"]
    /\ updateStateSeq(k)

    /\ UNCHANGED watch_list
    /\ pushKeyOrDoNothing(k)

    /\ UNCHANGED next_log
    /\ UNCHANGED main_vars
    /\ UNCHANGED <<watch_pc, watch_keys, watch_state, watch_local_key>>


new_chan == [status |-> "Empty", data |-> nil]

NewWatchChan(c) ==
    LET
        new_watch_ch == [watch_chan EXCEPT ![c] = new_chan]
    IN
        /\ watch_pc[c] = "Init"
        /\ watch_pc' = [watch_pc EXCEPT ![c] = "WaitOnChan"]

        /\ UNCHANGED server_vars
        /\ pushToClientOrDoNothing(c, new_watch_ch)

        /\ UNCHANGED <<watch_keys, watch_state, watch_local_key>>
        /\ UNCHANGED main_vars


active_keys == {k \in Key: db[k] # nil /\ db[k].status = "Running"}

UpdateWatchKeys(c) ==
    /\ watch_keys[c] # active_keys
    /\ watch_keys' = [watch_keys EXCEPT ![c] = active_keys]
    /\ UNCHANGED <<watch_pc, watch_chan, watch_seq, watch_log_index, watch_state>>
    /\ UNCHANGED watch_local_key
    /\ UNCHANGED main_vars
    /\ UNCHANGED server_vars


updateServerWatchList(c) ==
    LET
        old_set(k) == watch_list[k]
        new_set(k) ==
            IF k \in watch_keys[c]
                THEN old_set(k) \union {c}
                ELSE old_set(k) \ {c}
    IN
        watch_list' = [k \in Key |-> new_set(k)]


serverWatchClientKeys(c) == {k \in Key: c \in watch_list[k]}

AddToWaitList(c) ==
    /\ watch_keys[c] # serverWatchClientKeys(c)
    /\ updateServerWatchList(c)

    /\ UNCHANGED <<state, next_seq, state_seq>>
    /\ pushToClientOrDoNothing(c, watch_chan)

    /\ UNCHANGED <<watch_pc, watch_keys, watch_state, watch_local_key>>
    /\ UNCHANGED main_vars
    /\ UNCHANGED next_log


updateStateFromChan(c) ==
    LET
        k == watch_chan[c].data.key
        type == watch_chan[c].data.type
        log_line == watch_chan[c].data.line
    
        old_state == watch_state[c][k]

        old_logs ==
            IF old_state = nil
                THEN <<>>
                ELSE old_state.logs

        new_state ==
            [logs |-> Append(old_logs, log_line), status |-> "Running"]

        do_add_log ==
            /\ watch_state' = [
                    watch_state EXCEPT ![c][k] = new_state]
            /\ UNCHANGED watch_local_key
            /\ watch_pc' = [watch_pc EXCEPT ![c] = "Init"]

        do_complete ==
            /\ watch_state' = [
                    watch_state EXCEPT
                        ![c][k] = [logs |-> old_logs, status |-> "Completed"]]
            /\ watch_local_key' = [watch_local_key EXCEPT ![c] = k]
            /\ watch_pc' = [watch_pc EXCEPT ![c] = "UpdateDB"]
    IN
        IF type = "AddLog"
            THEN do_add_log
            ELSE do_complete

ConsumeWatchChan(c) ==
    /\ watch_pc[c] = "WaitOnChan"
    /\ watch_chan[c].status = "Ready"

    /\ watch_chan' = [
            watch_chan EXCEPT
                ![c].status = "Consumed",
                ![c].data = nil]
    
    /\ updateStateFromChan(c)
    
    /\ UNCHANGED <<watch_keys, watch_seq, watch_log_index>>
    /\ UNCHANGED main_vars
    /\ UNCHANGED server_vars


UpdateDB(c) ==
    LET
        k == watch_local_key[c]
    IN
        /\ watch_pc[c] = "UpdateDB"
        /\ watch_pc' = [watch_pc EXCEPT ![c] = "Init"]

        /\ db' = [db EXCEPT ![k] = watch_state[c][k]]
        /\ watch_local_key' = [watch_local_key EXCEPT ![c] = nil]

        /\ UNCHANGED <<watch_keys, watch_chan, watch_seq>>
        /\ UNCHANGED <<watch_log_index, watch_state>>
        /\ UNCHANGED server_vars
        /\ UNCHANGED <<pc, current_key>>


TerminateCond ==
    /\ \A k \in Key: db[k] # nil
    /\ \A k \in Key: state[k] # nil /\ state[k].status = "Completed"
    /\ \A c \in WatchClient:
        /\ watch_pc[c] = "WaitOnChan"
        /\ watch_keys[c] = active_keys
        /\ watch_keys[c] = serverWatchClientKeys(c)
        /\ watch_chan[c].status = "Empty"

Terminated ==
    /\ TerminateCond
    /\ UNCHANGED vars


Next ==
    \/ \E k \in Key:
        \/ AddDBJob(k)
        \/ ProduceLog(k)
        \/ FinishJob(k)
    \/ PushJob

    \/ \E c \in WatchClient:
        \/ NewWatchChan(c)
        \/ UpdateWatchKeys(c)
        \/ AddToWaitList(c)
        \/ ConsumeWatchChan(c)
        \/ UpdateDB(c)

    \/ Terminated

Spec == Init /\ [][Next]_vars

FairSpec == Spec /\ WF_vars(Next)


AlwaysTerminate == <> TerminateCond


AllJobsMustBeFinished ==
    TerminateCond =>
        \A k \in Key: db[k] # nil /\ db[k].status = "Completed"


DBShouldSameAsMem ==
    TerminateCond =>
        \A k \in Key: db[k] = state[k]


Sym == Permutations(Key)

====

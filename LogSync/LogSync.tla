-- ---- MODULE LogSync ----
EXTENDS TLC, Naturals, Sequences

CONSTANTS Key, WatchClient, nil

\* state is in-memory data
\* db is the same data but on the db
\* watch_chan is the receive channel for client
VARIABLES pc, current_key, db, 
    state, state_seq, next_log, next_seq, wait_list,
    watch_pc, watch_keys, watch_chan, watch_seq,
    watch_log_index, watch_state, watch_local_key,
    num_client_restart, num_main_restart, num_delete_state

main_vars == <<pc, current_key, db>>

watch_vars == <<watch_pc, watch_keys, watch_chan,
    watch_seq, watch_log_index, watch_state, watch_local_key>>

server_vars == <<state, state_seq, next_log, next_seq, wait_list>>

aux_vars == <<num_client_restart, num_main_restart, num_delete_state>>

vars == <<main_vars, server_vars, watch_vars, aux_vars>>


max_log_size == 3

max_client_restart == 1
max_main_restart == 1
max_delete_state == 1

Status == {"Running", "Completed", "Gone"}

LogEntry == 20..30

SeqMaxLen(S, n) == UNION {[1..m -> S] : m \in 0..n}

Info == [logs: Seq(LogEntry), status: Status]

NullInfo == Info \union {nil}

NullKey == Key \union {nil}

NullLogEntry == LogEntry \union {nil}

Event == [
    type: {"AddLog", "Finished", "JobGone"},
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
    /\ wait_list \in [Key -> SUBSET WatchClient]

    /\ watch_pc \in [WatchClient -> WatchState]
    /\ watch_keys \in [WatchClient -> SUBSET Key]
    /\ watch_chan \in [WatchClient -> Channel]
    /\ watch_seq \in [WatchClient -> [Key -> StateSeq]]
    /\ watch_log_index \in [WatchClient -> [Key -> Nat]]
    /\ watch_state \in [WatchClient -> [Key -> NullInfo]]
    /\ watch_local_key \in [WatchClient -> NullKey]

    /\ num_client_restart \in 0..max_client_restart
    /\ num_main_restart \in 0..max_main_restart
    /\ num_delete_state \in 0..max_delete_state


consumed_chan == [status |-> "Consumed", data |-> nil]

Init ==
    /\ pc = "Init"
    /\ current_key = nil
    /\ db = [k \in Key |-> nil]

    /\ state = [k \in Key |-> nil]
    /\ state_seq = [k \in Key |-> 100]
    /\ next_log = 20
    /\ wait_list = [k \in Key |-> {}]
    /\ next_seq = 100

    /\ watch_pc = [c \in WatchClient |-> "Init"]
    /\ watch_keys = [c \in WatchClient |-> {}]
    /\ watch_chan = [c \in WatchClient |-> consumed_chan]
    /\ watch_seq = [c \in WatchClient |-> [k \in Key|-> 100]]
    /\ watch_log_index = [c \in WatchClient |-> [k \in Key |-> 0]]
    /\ watch_state = [c \in WatchClient |-> [k \in Key |-> nil]]
    /\ watch_local_key = [c \in WatchClient |-> nil]

    /\ num_client_restart = 0
    /\ num_main_restart = 0
    /\ num_delete_state = 0


newJob == [logs |-> <<>>, status |-> "Running"]


AddDBJob(k) ==
    /\ pc = "Init"
    /\ db[k] = nil
    /\ pc' = "PushJob"
    /\ current_key' = k
    /\ db' = [db EXCEPT ![k] = newJob]
    /\ UNCHANGED server_vars
    /\ UNCHANGED watch_vars
    /\ UNCHANGED aux_vars


updateStateSeq(k) ==
    /\ next_seq' = next_seq + 1
    /\ state_seq' = [state_seq EXCEPT ![k] = next_seq']


PushJob ==
    /\ pc = "PushJob"
    /\ pc' = "Init"
    /\ current_key' = nil
    /\ state' = [state EXCEPT ![current_key] = db[current_key]]
    /\ UNCHANGED <<next_seq, state_seq>>
    /\ UNCHANGED wait_list
    /\ UNCHANGED db
    /\ UNCHANGED next_log
    /\ UNCHANGED watch_vars
    /\ UNCHANGED aux_vars


canPushKeyToClient(k, c, old_watch_ch) ==
    /\ old_watch_ch[c].status = "Empty"
    /\ c \in wait_list'[k]
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

        finished_or_gone ==
            IF state'[k].status = "Gone"
                THEN "JobGone"
                ELSE "Finished"
        
        finish_event == [
            type |-> finished_or_gone,
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

    /\ UNCHANGED wait_list
    /\ pushKeyOrDoNothing(k)

    /\ UNCHANGED main_vars
    /\ UNCHANGED <<watch_pc, watch_keys, watch_state, watch_local_key>>
    /\ UNCHANGED aux_vars


FinishJob(k) ==
    /\ state[k] # nil
    /\ state[k].status = "Running"
    /\ state' = [state EXCEPT ![k].status = "Completed"]
    /\ updateStateSeq(k)

    /\ UNCHANGED wait_list
    /\ pushKeyOrDoNothing(k)

    /\ UNCHANGED next_log
    /\ UNCHANGED main_vars
    /\ UNCHANGED <<watch_pc, watch_keys, watch_state, watch_local_key>>
    /\ UNCHANGED aux_vars


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
        /\ UNCHANGED aux_vars


active_keys ==
    LET
        db_set == {k \in Key: db[k] # nil /\ db[k].status = "Running"}
    IN
        db_set \ {current_key}

UpdateWatchKeys(c) ==
    /\ watch_keys[c] # active_keys
    /\ watch_keys' = [watch_keys EXCEPT ![c] = active_keys]
    /\ UNCHANGED <<watch_pc, watch_chan, watch_seq, watch_log_index, watch_state>>
    /\ UNCHANGED watch_local_key
    /\ UNCHANGED main_vars
    /\ UNCHANGED server_vars
    /\ UNCHANGED aux_vars


updateServerWaitList(c) ==
    LET
        old_set(k) == wait_list[k]
        new_set(k) ==
            IF k \in watch_keys[c]
                THEN old_set(k) \union {c}
                ELSE old_set(k) \ {c}
    IN
        wait_list' = [k \in Key |-> new_set(k)]


serverWatchClientKeys(c) == {k \in Key: c \in wait_list[k]}

createPlaceHolderStateForWaitList ==
    LET
        in_wait_list(k) == wait_list'[k] # {}

        keysWithNilState ==
            {k \in Key: in_wait_list(k) /\ state[k] = nil}

        new_state_fn(k) ==
            IF k \in keysWithNilState
                THEN [logs |-> <<>>, status |-> "Gone"]
                ELSE state[k]

        new_seq_fn(k) ==
            IF k \in keysWithNilState
                THEN next_seq'
                ELSE state_seq[k]

        update_state ==
            /\ next_seq' = next_seq + 1
            /\ state' = [k \in Key |-> new_state_fn(k)]
            /\ state_seq' = [k \in Key |-> new_seq_fn(k)]

        do_nothing ==
            UNCHANGED <<state, next_seq, state_seq>>
    IN
        IF keysWithNilState # {}
            THEN update_state
            ELSE do_nothing


AddToWaitList(c) ==
    /\ watch_keys[c] # serverWatchClientKeys(c)
    /\ updateServerWaitList(c)

    /\ createPlaceHolderStateForWaitList
    /\ pushToClientOrDoNothing(c, watch_chan)

    /\ UNCHANGED <<watch_pc, watch_keys, watch_state, watch_local_key>>
    /\ UNCHANGED main_vars
    /\ UNCHANGED next_log
    /\ UNCHANGED aux_vars


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

        new_status ==
            IF type = "JobGone"
                THEN "Gone"
                ELSE "Completed"

        do_complete ==
            /\ watch_state' = [
                watch_state EXCEPT
                    ![c][k] = [logs |-> old_logs, status |-> new_status]]
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
    /\ UNCHANGED aux_vars


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
        /\ UNCHANGED aux_vars


ClientRestart(c) ==
    /\ num_client_restart < max_client_restart
    /\ num_client_restart' = num_client_restart + 1
    /\ watch_chan' = [watch_chan EXCEPT ![c] = consumed_chan]
    /\ watch_keys' = [watch_keys EXCEPT ![c] = {}]
    /\ watch_local_key' = [watch_local_key EXCEPT ![c] = nil]
    /\ watch_log_index' = [watch_log_index EXCEPT ![c] = [k \in Key |-> 0]]
    /\ watch_seq' = [watch_seq EXCEPT ![c] = [k \in Key |-> 100]]
    /\ watch_state' = [watch_state EXCEPT ![c] = [k \in Key |-> nil]]
    /\ watch_pc' = [watch_pc EXCEPT ![c] = "Init"]
    /\ UNCHANGED server_vars
    /\ UNCHANGED main_vars
    /\ UNCHANGED <<num_main_restart, num_delete_state>>


MainRestart ==
    /\ num_main_restart < max_main_restart
    /\ num_main_restart' = num_main_restart + 1
    /\ current_key' = nil
    /\ pc' = "Init"
    /\ UNCHANGED db
    /\ UNCHANGED <<num_client_restart, num_delete_state>>
    /\ UNCHANGED server_vars
    /\ UNCHANGED watch_vars


DeleteRandomKeyInState(k) ==
    /\ num_delete_state < max_delete_state
    /\ num_delete_state' = num_delete_state + 1
    /\ state[k] # nil

    /\ state' = [state EXCEPT ![k] = nil]
    /\ state_seq' = [state_seq EXCEPT ![k] = 100]
    /\ wait_list' = [wait_list EXCEPT ![k] = {}]

    /\ UNCHANGED <<next_log, next_seq>>
    /\ UNCHANGED <<num_client_restart, num_main_restart>>
    /\ UNCHANGED main_vars
    /\ UNCHANGED watch_vars



statusIsFinished(st) ==
    \/ st = "Completed"
    \/ st = "Gone"

TerminateCond ==
    /\ \A k \in Key: db[k] # nil /\ statusIsFinished(db[k].status)
    /\ \A k \in Key: state[k] # nil => statusIsFinished(state[k].status)
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
        \/ DeleteRandomKeyInState(k)
    \/ PushJob

    \/ \E c \in WatchClient:
        \/ NewWatchChan(c)
        \/ UpdateWatchKeys(c)
        \/ AddToWaitList(c)
        \/ ConsumeWatchChan(c)
        \/ UpdateDB(c)
        \/ ClientRestart(c)

    \/ MainRestart

    \/ Terminated

Spec == Init /\ [][Next]_vars

FairSpec == Spec /\ WF_vars(Next)


AlwaysTerminate == <> TerminateCond


AllJobsMustBeFinished ==
    TerminateCond =>
        \A k \in Key: db[k] # nil /\ statusIsFinished(db[k].status)


infoEqual(db_val, state_val) ==
    /\ db_val.status \in {"Completed", "Gone"}
    /\ state_val.status \in {"Completed", "Gone"}

    /\ state_val.status = "Completed" => db_val.logs = state_val.logs
    /\ state_val.status = "Completed" => db_val.status = "Completed"

DBShouldSameAsMem ==
    TerminateCond =>
        \A k \in Key: state[k] # nil => infoEqual(db[k], state[k])


DBShouldSameAsMemWhenNoRestart ==
    LET
        cond ==
            /\ TerminateCond
            /\ num_main_restart = 0
            /\ num_delete_state = 0
    IN
        cond => \A k \in Key: state[k] = db[k] /\ db[k].status = "Completed"


StateAlwaysMatchWaitList ==
    \A k \in Key:
        wait_list[k] # {} => state[k] # nil


StateAlwaysMatchSeq ==
    \A k \in Key:
        state[k] = nil => state_seq[k] = 100


channelInitByClient(c) ==
    /\ watch_chan[c].status = "Consumed"
    /\ watch_chan[c].data = nil

channelInit == \A c \in WatchClient: channelInitByClient(c)

channelNextByClient(c) ==
    \/ /\ watch_chan[c].status = "Empty"
       /\ watch_chan'[c].status = "Ready"
       /\ watch_chan'[c].data # nil

    \/ /\ watch_chan[c].status = "Consumed"
       /\ watch_chan'[c].status = "Empty"
       /\ watch_chan'[c].data = nil

    \/ /\ watch_chan[c].status = "Consumed"
       /\ watch_chan'[c].status = "Ready"
       /\ watch_chan'[c].data # nil

    \/ /\ \/ watch_chan[c].status = "Ready"
          \/ watch_chan[c].status = "Empty"
       /\ watch_chan'[c].status = "Consumed"
       /\ watch_chan'[c].data = nil

channelNextActions == \E c \in WatchClient: channelNextByClient(c)

ChannelSpec ==
    channelInit /\ [][channelNextActions]_watch_chan


Sym == Permutations(Key)

====

-- ---- MODULE LogSync ----
EXTENDS TLC, Naturals, Sequences

CONSTANTS Key, WatchClient, nil

\* state is in-memory data
\* db is the same data but on the db
\* watch_info[c].chan is the receive channel for client
VARIABLES pc, current_key, db, 
    state, state_seq, next_log, next_seq, wait_list, lru_keys,
    watch_pc,
    watch_keys, watch_key_pc,
    watch_info,
    watch_state, watch_local_key, watch_local_info,
    num_client_restart, num_main_restart, num_delete_state

main_vars == <<pc, current_key, db>>

watch_local_vars == <<
    watch_pc, watch_state,
    watch_local_key, watch_local_info>>

watch_key_vars == <<watch_keys, watch_key_pc>>

watch_remove_vars == <<watch_info>>

watch_vars == <<watch_local_vars, watch_key_vars, watch_remove_vars>>

server_vars == <<state, state_seq, next_log, next_seq, wait_list, lru_keys>>

aux_vars == <<num_client_restart, num_main_restart, num_delete_state>>

vars == <<
    main_vars, server_vars,
    watch_local_vars, watch_key_vars, watch_remove_vars,
    aux_vars>>


max_log_size == 3

max_client_restart == 1
max_main_restart == 1
max_delete_state == 2

Status == {"Running", "Completed", "Gone"}

LogEntry == 20..30

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

WatchInfo == [
    chan: Channel,
    seq: [Key -> StateSeq],
    log_index: [Key -> Nat],
    keys: SUBSET Key
]

TypeOK ==
    /\ pc \in {"Init", "PushJob"}
    /\ current_key \in NullKey
    /\ db \in [Key -> NullInfo]

    /\ state \in [Key -> NullInfo]
    /\ state_seq \in [Key -> StateSeq]
    /\ next_log \in LogEntry
    /\ next_seq \in StateSeq
    /\ wait_list \in [Key -> SUBSET WatchClient]
    /\ lru_keys \subseteq Key

    /\ watch_pc \in [WatchClient -> WatchState]
    /\ watch_keys \in [WatchClient -> SUBSET Key]
    /\ watch_key_pc \in [WatchClient -> {"Init", "SetWaitList"}]
    /\ watch_info \in [WatchClient -> WatchInfo]
    /\ watch_state \in [WatchClient -> [Key -> NullInfo]]
    /\ watch_local_key \in [WatchClient -> NullKey]
    /\ watch_local_info \in [WatchClient -> NullInfo]

    /\ num_client_restart \in 0..max_client_restart
    /\ num_main_restart \in 0..max_main_restart
    /\ num_delete_state \in 0..max_delete_state


consumed_chan == [status |-> "Consumed", data |-> nil]

init_info == [
    chan |-> consumed_chan,
    seq |-> [k \in Key |-> 100],
    log_index |-> [k \in Key |-> 0],
    keys |-> {}
]

Init ==
    /\ pc = "Init"
    /\ current_key = nil
    /\ db = [k \in Key |-> nil]

    /\ state = [k \in Key |-> nil]
    /\ state_seq = [k \in Key |-> 100]
    /\ next_log = 20
    /\ wait_list = [k \in Key |-> {}]
    /\ next_seq = 100
    /\ lru_keys = {}

    /\ watch_pc = [c \in WatchClient |-> "Init"]
    /\ watch_keys = [c \in WatchClient |-> {}]
    /\ watch_key_pc = [c \in WatchClient |-> "Init"]
    /\ watch_info = [c \in WatchClient |-> init_info]
    /\ watch_state = [c \in WatchClient |-> [k \in Key |-> nil]]
    /\ watch_local_key = [c \in WatchClient |-> nil]
    /\ watch_local_info = [c \in WatchClient |-> nil]

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
    /\ lru_keys' = lru_keys \union {current_key}
    /\ UNCHANGED <<next_seq, state_seq>>
    /\ UNCHANGED wait_list
    /\ UNCHANGED db
    /\ UNCHANGED next_log
    /\ UNCHANGED watch_vars
    /\ UNCHANGED aux_vars


canPushKeyToClient(k, c, old_info) ==
    /\ old_info.chan.status = "Empty"
    /\ c \in wait_list'[k]
    /\ old_info.seq[k] < state_seq'[k]

pushToClientChan(k, c, old_info) ==
    LET
        last_index == old_info.log_index[k]
        state_index == Len(state'[k].logs)
        new_index == last_index + 1

        new_line == state'[k].logs[new_index]

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

        add_log_cond == last_index < state_index \/ is_running

        update_seq_cond ==
            \/ last_index >= state_index
            \/ new_index >= state_index /\ is_running
        
        new_event ==
            IF add_log_cond
                THEN add_event
                ELSE finish_event
        
        new_chan == [status |-> "Ready", data |-> new_event]

        new_log_index == [old_info.log_index EXCEPT ![k] = new_index]

        new_seq == [
            old_info.seq EXCEPT ![k] =
                IF update_seq_cond
                    THEN state_seq'[k]
                    ELSE old_info.seq[k]
            ]

        new_info == [
            chan |-> new_chan,
            seq |-> new_seq,
            log_index |-> new_log_index,
            keys |-> old_info.keys]
    IN
        watch_info' = [watch_info EXCEPT ![c] = new_info]


pushToClientOrDoNothing(c, old_info) ==
    LET
        doNothing ==
            /\ \A k \in Key: ~canPushKeyToClient(k, c, old_info)
            /\ watch_info' = [watch_info EXCEPT ![c] = old_info]
    IN
    \/ \E k \in Key:
        /\ canPushKeyToClient(k, c, old_info)
        /\ pushToClientChan(k, c, old_info)
    \/ doNothing


pushKeyOrDoNothing(k) ==
    LET
        doPush ==
            \E c \in WatchClient:
                /\ canPushKeyToClient(k, c, watch_info[c])
                /\ pushToClientChan(k, c, watch_info[c])

        doNothing ==
            /\ \A c \in WatchClient: ~canPushKeyToClient(k, c, watch_info[c])
            /\ UNCHANGED watch_info
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

    /\ UNCHANGED lru_keys
    /\ UNCHANGED main_vars
    /\ UNCHANGED watch_local_vars
    /\ UNCHANGED watch_key_vars
    /\ UNCHANGED aux_vars


FinishJob(k) ==
    /\ state[k] # nil
    /\ state[k].status = "Running"
    /\ state' = [state EXCEPT ![k].status = "Completed"]
    /\ updateStateSeq(k)

    /\ UNCHANGED wait_list
    /\ pushKeyOrDoNothing(k)

    /\ UNCHANGED lru_keys
    /\ UNCHANGED next_log
    /\ UNCHANGED main_vars
    /\ UNCHANGED watch_local_vars
    /\ UNCHANGED watch_key_vars
    /\ UNCHANGED aux_vars



NewWatchChan(c) ==
    LET
        new_chan == [status |-> "Empty", data |-> nil]

        new_info == [watch_info[c] EXCEPT !.chan = new_chan]
    IN
        /\ watch_pc[c] = "Init"
        /\ watch_pc' = [watch_pc EXCEPT ![c] = "WaitOnChan"]

        /\ UNCHANGED server_vars
        /\ pushToClientOrDoNothing(c, new_info)

        /\ UNCHANGED <<watch_keys, watch_key_pc>>
        /\ UNCHANGED <<watch_state, watch_local_key, watch_local_info>>
        /\ UNCHANGED main_vars
        /\ UNCHANGED aux_vars


active_keys ==
    LET
        db_set == {k \in Key: db[k] # nil /\ db[k].status = "Running"}
    IN
        db_set \ {current_key}


clearWatchStateKeyNotInSet(c, set) ==
    [k \in Key |-> IF k \in set THEN watch_state[c][k] ELSE nil]

UpdateWatchKeys(c) ==
    /\ watch_key_pc[c] = "Init"
    /\ watch_keys[c] # active_keys
    /\ watch_key_pc' = [watch_key_pc EXCEPT ![c] = "SetWaitList"]

    /\ watch_keys' = [watch_keys EXCEPT ![c] = active_keys]
    /\ watch_state' = [watch_state EXCEPT
            ![c] = clearWatchStateKeyNotInSet(c, active_keys)]

    /\ UNCHANGED watch_remove_vars
    /\ UNCHANGED <<watch_pc>>
    /\ UNCHANGED <<watch_local_key, watch_local_info>>
    /\ UNCHANGED main_vars
    /\ UNCHANGED server_vars
    /\ UNCHANGED aux_vars


updateLRUKeys(c) ==
    LET
        removed == watch_info'[c].keys
        added == {k \in watch_info[c].keys: wait_list'[k] = {}}
    IN
        lru_keys' = (lru_keys \union added) \ removed

updateServerWaitList(c) ==
    LET
        old_set(k) == wait_list[k]
        new_set(k) ==
            IF k \in watch_keys[c]
                THEN old_set(k) \union {c}
                ELSE old_set(k) \ {c}
    IN
        wait_list' = [k \in Key |-> new_set(k)]

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


removeSeqLogIndexNotInWaitList(c) ==
    LET
        old_info == watch_info[c]

        in_list(k) == wait_list'[k] # {}

        new_seq ==
            [k \in Key |-> IF in_list(k) THEN old_info.seq[k] ELSE 100]

        new_log_index ==
            [k \in Key |-> IF in_list(k) THEN old_info.log_index[k] ELSE 0]
    IN
        [old_info EXCEPT
            !.seq = new_seq,
            !.log_index = new_log_index,
            !.keys = watch_keys[c]]

AddToWaitList(c) ==
    /\ watch_key_pc[c] = "SetWaitList"
    /\ watch_key_pc' = [watch_key_pc EXCEPT ![c] = "Init"]
    /\ updateServerWaitList(c)

    /\ createPlaceHolderStateForWaitList
    /\ LET
            new_info == removeSeqLogIndexNotInWaitList(c)
        IN
            pushToClientOrDoNothing(c, new_info)
    /\ updateLRUKeys(c)

    /\ UNCHANGED <<watch_keys>>
    /\ UNCHANGED watch_local_vars
    /\ UNCHANGED main_vars
    /\ UNCHANGED next_log
    /\ UNCHANGED aux_vars


updateStateFromChan(c) ==
    LET
        chan == watch_info[c].chan
        k == chan.data.key
        type == chan.data.type
        log_line == chan.data.line
    
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
            /\ UNCHANGED <<watch_local_key, watch_local_info>>
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

            /\ watch_local_info' = [
                watch_local_info EXCEPT ![c] = watch_state'[c][k]]

            /\ watch_pc' = [watch_pc EXCEPT ![c] = "UpdateDB"]

        do_nothing ==
            /\ watch_pc' = [watch_pc EXCEPT ![c] = "Init"]
            /\ UNCHANGED watch_state
            /\ UNCHANGED <<watch_local_key, watch_local_info>>
    IN
        IF k \in watch_keys[c]
            THEN IF type = "AddLog"
                THEN do_add_log
                ELSE do_complete
            ELSE do_nothing

ConsumeWatchChan(c) ==
    /\ watch_pc[c] = "WaitOnChan"
    /\ watch_info[c].chan.status = "Ready"

    /\ watch_info' = [
            watch_info EXCEPT
                ![c].chan.status = "Consumed",
                ![c].chan.data = nil]
    
    /\ updateStateFromChan(c)
    
    /\ UNCHANGED <<watch_keys, watch_key_pc>>
    /\ UNCHANGED main_vars
    /\ UNCHANGED server_vars
    /\ UNCHANGED aux_vars


UpdateDB(c) ==
    LET
        k == watch_local_key[c]
        info == watch_local_info[c]
    IN
        /\ watch_pc[c] = "UpdateDB"
        /\ watch_pc' = [watch_pc EXCEPT ![c] = "Init"]
        /\ db' = [db EXCEPT ![k] = info]
        /\ watch_local_key' = [watch_local_key EXCEPT ![c] = nil]
        /\ watch_local_info' = [watch_local_info EXCEPT ![c] = nil]
        /\ UNCHANGED watch_remove_vars
        /\ UNCHANGED <<watch_keys, watch_key_pc, watch_state>>
        /\ UNCHANGED server_vars
        /\ UNCHANGED <<pc, current_key>>
        /\ UNCHANGED aux_vars


removeClientFromWaitList(k, c) ==
    wait_list[k] \ {c}


ClientRestart(c) ==
    /\ num_client_restart < max_client_restart
    /\ num_client_restart' = num_client_restart + 1
    /\ watch_info' = [watch_info EXCEPT ![c] = init_info]
    /\ watch_keys' = [watch_keys EXCEPT ![c] = {}]

    /\ watch_local_key' = [watch_local_key EXCEPT ![c] = nil]
    /\ watch_local_info' = [watch_local_info EXCEPT ![c] = nil]

    /\ watch_state' = [watch_state EXCEPT ![c] = [k \in Key |-> nil]]
    /\ watch_pc' = [watch_pc EXCEPT ![c] = "Init"]
    /\ wait_list' = [k \in Key |-> removeClientFromWaitList(k, c)]
    /\ watch_key_pc' = [watch_key_pc EXCEPT ![c] = "Init"]
    /\ updateLRUKeys(c)

    /\ UNCHANGED <<state, state_seq, next_log, next_seq>>
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
    /\ k \in lru_keys

    /\ state' = [state EXCEPT ![k] = nil]
    /\ state_seq' = [state_seq EXCEPT ![k] = 100]
    /\ wait_list' = [wait_list EXCEPT ![k] = {}]
    /\ lru_keys' = lru_keys \ {k}

    /\ UNCHANGED <<next_log, next_seq>>
    /\ UNCHANGED <<num_client_restart, num_main_restart>>
    /\ UNCHANGED main_vars
    /\ UNCHANGED watch_local_vars
    /\ UNCHANGED watch_key_vars
    /\ UNCHANGED watch_remove_vars


statusIsFinished(st) ==
    \/ st = "Completed"
    \/ st = "Gone"

serverWatchClientKeys(c) == {k \in Key: c \in wait_list[k]}

TerminateCond ==
    /\ \A k \in Key: db[k] # nil /\ statusIsFinished(db[k].status)
    /\ \A k \in Key: state[k] # nil => statusIsFinished(state[k].status)
    /\ \A c \in WatchClient:
        /\ watch_pc[c] = "WaitOnChan"
        /\ watch_keys[c] = active_keys
        /\ watch_keys[c] = serverWatchClientKeys(c)
        /\ watch_info[c].chan.status = "Empty"

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


WatchKeysMatchWatchState ==
    \A c \in WatchClient, k \in Key:
        ~(k \in watch_keys[c]) => watch_state[c][k] = nil


WatchListMatchSeqAndLogIndex ==
    \A c \in WatchClient, k \in Key:
        ~(c \in wait_list[k]) =>
            /\ watch_info[c].seq[k] = 100
            /\ watch_info[c].log_index[k] = 0


LRUKeysMatchWaitList ==
    lru_keys = {k \in Key: state[k] # nil /\ wait_list[k] = {}}


InfoKeysMatchSeq ==
    \A c \in WatchClient, k \in Key:
        /\ watch_info[c].seq[k] > 100 => k \in watch_info[c].keys
        /\ watch_info[c].log_index[k] > 0 => k \in watch_info[c].keys


channelInitByClient(c) ==
    /\ watch_info[c].chan.status = "Consumed"
    /\ watch_info[c].chan.data = nil

channelInit == \A c \in WatchClient: channelInitByClient(c)

channelNextByClient(c) ==
    LET
        old_chan == watch_info[c].chan
        new_chan == watch_info'[c].chan

        empty_to_ready ==
            /\ old_chan.status = "Empty"
            /\ new_chan.status = "Ready"
            /\ new_chan.data # nil

        consumed_to_empty ==
            /\ old_chan.status = "Consumed"
            /\ new_chan.status = "Empty"
            /\ new_chan.data = nil

        consumed_to_ready ==
            /\ old_chan.status = "Consumed"
            /\ new_chan.status = "Ready"
            /\ new_chan.data # nil

        to_consumed ==
            /\ \/ old_chan.status = "Ready"
               \/ old_chan.status = "Empty"
            /\ new_chan.status = "Consumed"
            /\ new_chan.data = nil
    IN
        \/ empty_to_ready
        \/ consumed_to_empty
        \/ consumed_to_ready
        \/ to_consumed
        \/ new_chan = old_chan \* UNCHANGED

channelNextActions == \E c \in WatchClient: channelNextByClient(c)

ChannelSpec ==
    channelInit /\ [][channelNextActions]_watch_info


ChannelAddLogNonEmpty ==
    \A c \in WatchClient:
        LET
            chan == watch_info[c].chan
            cond ==
                /\ chan.status = "Ready"
                /\ chan.data.type = "AddLog"
        IN
            cond => chan.data.line > 0


LogShouldMatchWhenRunning ==
    \A k \in Key, c \in WatchClient:
        LET
            cond ==
                /\ state[k] # nil
                /\ state[k].status = "Running"
                /\ Len(state[k].logs) > 0
                /\ watch_pc[c] = "WaitOnChan"
                /\ watch_info[c].chan.status = "Empty"
                /\ watch_keys[c] = active_keys
                /\ watch_keys[c] = serverWatchClientKeys(c)
        IN
            cond => watch_state[c][k] = state[k]


Sym == Permutations(Key)

====

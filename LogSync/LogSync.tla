-- ---- MODULE LogSync ----
EXTENDS TLC, Naturals, Sequences

CONSTANTS Key, WatchClient, nil

\* state is in-memory data
\* db is the same data but on the db
\* watch_chan is the receive channel for client
VARIABLES pc, current_key, db, 
    state, next_log, watch_list,
    watch_pc, watch_keys, watch_chan

main_vars == <<pc, current_key, db>>

watch_vars == <<watch_pc, watch_keys, watch_chan>>

server_vars == <<state, next_log, watch_list>>

vars == <<main_vars, server_vars, watch_vars>>


max_log_size == 3

Status == {"Running", "Completed", "Gone"}

Info == [logs: Seq(Nat), status: Status]

NullInfo == Info \union {nil}

NullKey == Key \union {nil}

Event == [type: {"AddLog", "Finished"}, index: Nat, line: Nat]

NullEvent == Event \union {nil}

Channel == [status: {"Empty", "Ready", "Consumed"}, data: NullEvent]

NullChannel == Channel \union {nil}

TypeOK ==
    /\ pc \in {"Init", "PushJob"}
    /\ current_key \in NullKey
    /\ db \in [Key -> NullInfo]

    /\ state \in [Key -> NullInfo]
    /\ next_log \in Nat
    /\ watch_list \in [Key -> SUBSET WatchClient]

    /\ watch_pc \in [WatchClient -> {"Init", "AddToWaitList", "WaitOnChan"}]
    /\ watch_keys \in [WatchClient -> SUBSET Key]
    /\ watch_chan \in [WatchClient -> NullChannel]


Init ==
    /\ pc = "Init"
    /\ current_key = nil
    /\ db = [k \in Key |-> nil]

    /\ state = [k \in Key |-> nil]
    /\ next_log = 20
    /\ watch_list = [k \in Key |-> {}]

    /\ watch_pc = [c \in WatchClient |-> "Init"]
    /\ watch_keys = [c \in WatchClient |-> {}]
    /\ watch_chan = [c \in WatchClient |-> nil]


newJob == [logs |-> <<>>, status |-> "Running"]


AddDBJob(k) ==
    /\ pc = "Init"
    /\ state[k] = nil
    /\ pc' = "PushJob"
    /\ current_key' = k
    /\ db' = [db EXCEPT ![k] = newJob]
    /\ UNCHANGED server_vars
    /\ UNCHANGED watch_vars


PushJob ==
    /\ pc = "PushJob"
    /\ pc' = "Init"
    /\ current_key' = nil
    /\ state' = [state EXCEPT ![current_key] = db[current_key]]
    /\ UNCHANGED watch_list
    /\ UNCHANGED db
    /\ UNCHANGED next_log
    /\ UNCHANGED watch_vars


ProduceLog(k) ==
    /\ state[k] # nil
    /\ state[k].status = "Running"
    /\ Len(state[k].logs) < max_log_size
    /\ next_log' = next_log + 1
    /\ state' = [state EXCEPT ![k].logs = Append(@, next_log')]
    /\ UNCHANGED watch_list \* TODO
    /\ UNCHANGED main_vars
    /\ UNCHANGED watch_vars


FinishJob(k) ==
    /\ state[k] # nil
    /\ state[k].status = "Running"
    /\ state' = [state EXCEPT ![k].status = "Completed"]
    /\ UNCHANGED watch_list \* TODO
    /\ UNCHANGED next_log
    /\ UNCHANGED main_vars
    /\ UNCHANGED watch_vars



new_chan == [status |-> "Empty", data |-> nil]

NewWatchChan(c) ==
    /\ watch_pc[c] = "Init"
    /\ watch_pc' = [watch_pc EXCEPT ![c] = "AddToWaitList"]
    /\ watch_chan' = [watch_pc EXCEPT ![c] = new_chan]
    /\ UNCHANGED watch_keys
    /\ UNCHANGED main_vars
    /\ UNCHANGED server_vars



addClientToWatchList(c) ==
    LET
        old_set(k) == watch_list[k]
        new_set(k) ==
            IF k \in watch_keys[c]
                THEN old_set(k) \union {c}
                ELSE old_set(k)
    IN
        watch_list' = [k \in Key |-> new_set(k)]

AddToWaitList(c) ==
    /\ watch_pc[c] = "AddToWaitList"
    /\ watch_pc' = [watch_pc EXCEPT ![c] = "WaitOnChan"]
    /\ addClientToWatchList(c)
    /\ UNCHANGED state
    /\ UNCHANGED <<watch_chan, watch_keys>>
    /\ UNCHANGED main_vars
    /\ UNCHANGED next_log


TerminateCond ==
    /\ \A k \in Key: db[k] # nil
    /\ \A k \in Key: state[k] # nil => state[k].status = "Completed"
    /\ \A c \in WatchClient: watch_pc[c] = "WaitOnChan"

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
        \/ AddToWaitList(c)

    \/ Terminated


AllJobsMustBeFinished ==
    TerminateCond =>
        \A k \in Key: db[k] # nil /\ db[k].status = "Completed"


Spec == Init /\ [][Next]_vars


====

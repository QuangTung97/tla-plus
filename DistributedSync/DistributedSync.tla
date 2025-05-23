------ MODULE DistributedSync ----
EXTENDS TLC, Naturals, Sequences, FiniteSets

CONSTANTS Dataset, Node, Storage, nil,
    max_close_conn, max_value, max_sync_failed

VARIABLES
    config, active_conns, server_node_info,
    db, last_seq, failed_replicas,
    data, global_conn,
    node_conn, node_config, node_db, node_last_seq,
    node_events, node_pending_jobs,
    num_close_conn, dataset_sort_order,
    next_value, stop_delete, num_sync_failed

core_vars == <<
    config, active_conns, server_node_info,
    db, last_seq, failed_replicas
>>

node_vars == <<
    node_conn, node_config, node_db, node_last_seq,
    node_events, node_pending_jobs
>>

aux_vars == <<
    num_close_conn, dataset_sort_order,
    next_value, stop_delete, num_sync_failed
>>
vars == <<core_vars, data, global_conn, node_vars, aux_vars>>

-------------------------------------------------------------------------------

Range(f) == {f[x]: x \in DOMAIN f}

seq_not_duplicated(f) ==
    Cardinality(Range(f)) = Len(f)

-------------------------------------------------------------------------------

Value == 21..29
NullValue == Value \union {nil}

NullNode == Node \union {nil}

EventSeq == 30..39

Config == [
    primary: Storage,
    runner: Node,
    replicas: SUBSET Storage,
    deleted: BOOLEAN
]

NullConfig == Config \union {nil}

Request ==
    LET
        connect == [
            type: {"Connect"},
            node: Node,
            current: SUBSET Dataset
        ]

        new_entry == [
            type: {"NewEntry"},
            seq: EventSeq,
            ds: Dataset,
            storage: Storage,
            value: Value
        ]

        new_entry_failed == [
            type: {"NewEntryFailed"},
            seq: EventSeq,
            ds: Dataset,
            storage: Storage
        ]
    IN
        UNION {connect, new_entry, new_entry_failed}

Response ==
    LET
        conf_resp == [
            type: {"Config"},
            ds: Dataset,
            primary: Storage,
            replicas: SUBSET Storage,
            deleted: BOOLEAN
        ]

        connect_resp == [
            type: {"ConnectReply"},
            seq: EventSeq
        ]

        retry_resp == [
            type: {"RetryReplica"},
            ds: Dataset,
            storage: Storage
        ]
    IN
        UNION {conf_resp, connect_resp, retry_resp}

Conn == [
    send: Seq(Request),
    recv: Seq(Response),
    closed: BOOLEAN
]

ConnAddr == DOMAIN global_conn

NullConn == ConnAddr \union {nil}

ActiveConnInfo == [
    node: NullNode
]

Channel == [
    status: {"Empty", "Ready", "Nil"},
    data: Seq(Response)
]

new_empty_chan == [
    status |-> "Empty",
    data |-> <<>>
]

ServerNodeInfo == [
    conn: NullConn,
    chan: Channel,
    pending: Seq(Dataset),
    pending_set: SUBSET Dataset
]

nil_chan == [
    status |-> "Nil",
    data |-> <<>>
]

init_server_node_info == [
    conn |-> nil,
    chan |-> nil_chan,
    pending |-> <<>>,
    pending_set |-> {}
]


config_is_active(d, n) ==
    /\ config[d] # nil
    /\ config[d].runner = n
    /\ ~config[d].deleted

config_is_deleted(d, n) ==
    /\ config[d] # nil
    /\ config[d].runner = n
    /\ config[d].deleted

config_change_list(n) ==
    LET
        filter_fn(d) == config_is_active(d, n)
    IN
    SelectSeq(dataset_sort_order, filter_fn)

-------------------------------------------------------------------------------

num_dataset == Cardinality(Dataset)

TypeOK ==
    /\ config \in [Dataset -> NullConfig]
    /\ server_node_info \in [Node -> ServerNodeInfo]
    /\ active_conns \subseteq ConnAddr
    /\ db \in [Dataset -> [Storage -> NullValue]]
    /\ last_seq \in [Node -> EventSeq]
    /\ failed_replicas \in [Dataset -> SUBSET Storage]

    /\ data \in [Dataset -> [Storage -> NullValue]]
    /\ global_conn \in Seq(Conn)

    /\ node_conn \in [Node -> NullConn]
    /\ node_config \in [Node -> [Dataset -> NullConfig]]
    /\ node_db \in [Dataset -> [Storage -> NullValue]]
    /\ node_last_seq \in [Node -> EventSeq \union {nil}]
    /\ node_events \in [Node -> Seq(Request)]
    /\ node_pending_jobs \in [Node -> [Dataset -> SUBSET Storage]]

    /\ num_close_conn \in 0..max_close_conn
    /\ dataset_sort_order \in Seq(Dataset)
    /\ Range(dataset_sort_order) = Dataset
    /\ next_value \in 20..max_value
    /\ stop_delete \in BOOLEAN
    /\ num_sync_failed \in 0..max_sync_failed

Init ==
    /\ config = [d \in Dataset |-> nil]
    /\ server_node_info = [n \in Node |-> init_server_node_info]
    /\ active_conns = {}
    /\ db = [d \in Dataset |-> [s \in Storage |-> nil]]
    /\ last_seq = [n \in Node |-> 30]
    /\ failed_replicas = [d \in Dataset |-> {}]

    /\ data = [d \in Dataset |-> [s \in Storage |-> nil]]
    /\ global_conn = <<>>

    /\ node_conn = [n \in Node |-> nil]
    /\ node_config = [n \in Node |-> [d \in Dataset |-> nil]]
    /\ node_db = [d \in Dataset |-> [s \in Storage |-> nil]]
    /\ node_last_seq = [n \in Node |-> nil]
    /\ node_events = [n \in Node |-> <<>>]
    /\ node_pending_jobs = [n \in Node |-> [d \in Dataset |-> {}]]

    /\ num_close_conn = 0
    /\ dataset_sort_order \in [1..num_dataset -> Dataset]
    /\ Range(dataset_sort_order) = Dataset
    /\ next_value = 20
    /\ stop_delete = FALSE
    /\ num_sync_failed = 0

-------------------------------------------------------------------------------

new_config_resp(d) == [
    type |-> "Config",
    ds |-> d,
    primary |-> config'[d].primary,
    replicas |-> config'[d].replicas,
    deleted |-> config'[d].deleted
]

new_ready_chan(resp) == [
    status |-> "Ready",
    data |-> <<resp>>
]


updateConfigPushToChan(d, n) ==
    LET
        ch == server_node_info[n].chan
        conn == server_node_info[n].conn

        existed_in_pending_set ==
            d \in server_node_info[n].pending_set

        when_chan_nil ==
            /\ server_node_info' = [server_node_info EXCEPT
                    ![n].pending = Append(@, d),
                    ![n].pending_set = @ \union {d}
                ]

        when_chan_not_nil ==
            /\ server_node_info' = [server_node_info EXCEPT
                    ![n].chan = new_ready_chan(new_config_resp(d))
                ]
    IN
    IF conn = nil THEN
        UNCHANGED server_node_info
    ELSE IF ch.status \in {"Nil", "Ready"} THEN
        IF existed_in_pending_set THEN
            UNCHANGED server_node_info
        ELSE
            when_chan_nil
    ELSE
        when_chan_not_nil


SetupPrimaryConfig(d, n, s) ==
    LET
        new_config == [
            primary |-> s,
            runner |-> n,
            replicas |-> {},
            deleted |-> FALSE
        ]
    IN
    /\ config[d] = nil
    /\ config' = [config EXCEPT ![d] = new_config]
    /\ updateConfigPushToChan(d, n)
    /\ UNCHANGED <<db, last_seq, failed_replicas>>
    /\ UNCHANGED active_conns
    /\ UNCHANGED data
    /\ UNCHANGED node_vars
    /\ UNCHANGED global_conn
    /\ UNCHANGED aux_vars


AddReplicaConfig(d, s) ==
    /\ config[d] # nil
    /\ ~config[d].deleted
    /\ s \notin config[d].replicas
    /\ s # config[d].primary

    /\ config' = [config EXCEPT ![d].replicas = @ \union {s}]
    /\ updateConfigPushToChan(d, config[d].runner)

    /\ UNCHANGED global_conn
    /\ UNCHANGED <<db, last_seq, failed_replicas>>
    /\ UNCHANGED active_conns
    /\ UNCHANGED data
    /\ UNCHANGED node_vars
    /\ UNCHANGED aux_vars


DeleteConfig(d) ==
    LET
        n == config[d].runner

        filter_fn(x) == x # d

        remove_deleted(list) ==
            SelectSeq(list, filter_fn)
    IN
    /\ ~stop_delete
    /\ config[d] # nil
    /\ ~config[d].deleted
    /\ config' = [config EXCEPT ![d].deleted = TRUE]
    /\ updateConfigPushToChan(d, n)

    /\ UNCHANGED <<db, last_seq, failed_replicas>>
    /\ UNCHANGED global_conn
    /\ UNCHANGED active_conns
    /\ UNCHANGED data
    /\ UNCHANGED node_vars
    /\ UNCHANGED aux_vars


AcceptConn ==
    \E conn \in ConnAddr:
        LET
            info == [
                node |-> nil
            ]
        IN
        /\ conn \notin active_conns
        /\ ~global_conn[conn].closed
        /\ active_conns' = active_conns \union {conn}
        /\ UNCHANGED global_conn
        /\ UNCHANGED <<db, last_seq, failed_replicas>>
        /\ UNCHANGED server_node_info
        /\ UNCHANGED config
        /\ UNCHANGED data
        /\ UNCHANGED node_vars
        /\ UNCHANGED aux_vars


doHandleConnect(conn) ==
    LET
        req == global_conn[conn].send[1]
        n == req.node

        connect_resp == [
            type |-> "ConnectReply",
            seq |-> last_seq[n]
        ]

        filter_fn(d) ==
            \/ config_is_active(d, n)
            \/ /\ config_is_deleted(d, n)
               /\ d \in req.current

        pending_list == SelectSeq(dataset_sort_order, filter_fn)

        pending_ds == pending_list[1]

        when_pending_empty ==
            /\ server_node_info' = [server_node_info EXCEPT
                    ![n].conn = conn,
                    ![n].chan = new_empty_chan
                ]

        new_pending == Tail(pending_list)

        when_pending_non_empty ==
            /\ server_node_info' = [server_node_info EXCEPT
                    ![n].conn = conn,
                    ![n].pending = new_pending,
                    ![n].pending_set = Range(new_pending),
                    ![n].chan = new_ready_chan(new_config_resp(pending_ds))
                ]
    IN
    /\ conn \in active_conns
    /\ global_conn[conn].send # <<>>
    /\ req.type = "Connect"
    /\ global_conn' = [global_conn EXCEPT
            ![conn].send = Tail(@),
            ![conn].recv = Append(@, connect_resp)
        ]

    /\ UNCHANGED config
    /\ IF pending_list = <<>>
        THEN when_pending_empty
        ELSE when_pending_non_empty

    /\ UNCHANGED active_conns
    /\ UNCHANGED <<db, last_seq, failed_replicas>>
    /\ UNCHANGED data
    /\ UNCHANGED node_vars
    /\ UNCHANGED aux_vars

HandleConnect ==
    \E conn \in ConnAddr: doHandleConnect(conn)


HandleNewEntry(n) ==
    LET
        conn == server_node_info[n].conn
        req == global_conn[conn].send[1]

        d == req.ds
        s == req.storage
    IN
    /\ conn # nil
    /\ global_conn[conn].send # <<>>
    /\ req.type = "NewEntry"
    /\ global_conn' = [global_conn EXCEPT ![conn].send = Tail(@)]

    /\ db' = [db EXCEPT ![d][s] = req.value]
    /\ last_seq' = [last_seq EXCEPT ![n] = req.seq]
    /\ UNCHANGED failed_replicas

    /\ UNCHANGED config
    /\ UNCHANGED server_node_info
    /\ UNCHANGED active_conns
    /\ UNCHANGED data
    /\ UNCHANGED node_vars
    /\ UNCHANGED aux_vars


HandleNewEntryFailed(n) ==
    LET
        conn == server_node_info[n].conn
        req == global_conn[conn].send[1]

        d == req.ds
        s == req.storage
    IN
    /\ conn # nil
    /\ global_conn[conn].send # <<>>
    /\ req.type = "NewEntryFailed"
    /\ global_conn' = [global_conn EXCEPT ![conn].send = Tail(@)]

    /\ failed_replicas' = [failed_replicas EXCEPT ![d] = @ \union {s}]
    /\ last_seq' = [last_seq EXCEPT ![n] = req.seq]
    /\ UNCHANGED db

    /\ UNCHANGED config
    /\ UNCHANGED server_node_info
    /\ UNCHANGED active_conns
    /\ UNCHANGED data
    /\ UNCHANGED node_vars
    /\ UNCHANGED aux_vars


RetryFailedReplica(d, s) ==
    LET
        n == config[d].runner
        conn == server_node_info[n].conn

        retry_resp == [
            type |-> "RetryReplica",
            ds |-> d,
            storage |-> s
        ]
    IN
    /\ s \in failed_replicas[d]
    /\ ~global_conn[conn].closed
    /\ num_close_conn = max_close_conn

    /\ failed_replicas' = [failed_replicas EXCEPT ![d] = @ \ {s}]
    /\ global_conn' = [global_conn EXCEPT ![conn].recv = Append(@, retry_resp)]

    /\ UNCHANGED config
    /\ UNCHANGED data
    /\ UNCHANGED db
    /\ UNCHANGED last_seq
    /\ UNCHANGED server_node_info
    /\ UNCHANGED active_conns
    /\ UNCHANGED node_vars
    /\ UNCHANGED aux_vars


ConsumeChan(n) ==
    LET
        old_chan == server_node_info[n].chan
        resp == old_chan.data[1]

        consumed == [old_chan EXCEPT !.data = Tail(@), !.status = "Empty"]

        pending_list == server_node_info[n].pending
        pending_ds == pending_list[1]

        conn == server_node_info[n].conn

        when_empty ==
            /\ server_node_info' = [server_node_info
                    EXCEPT ![n].chan = consumed]

        pushed_ch == new_ready_chan(new_config_resp(pending_ds))

        d == server_node_info[n].pending[1]

        when_non_empty ==
            /\ server_node_info' = [server_node_info EXCEPT
                    ![n].chan = pushed_ch,
                    ![n].pending = Tail(@),
                    ![n].pending_set = @ \ {d}
                ]
    IN
    /\ server_node_info[n].chan.status = "Ready"
    /\ UNCHANGED config

    /\ IF pending_list = <<>>
        THEN when_empty
        ELSE when_non_empty

    /\ global_conn' = [global_conn EXCEPT
            ![conn].recv =
                IF global_conn[conn].closed
                    THEN @
                    ELSE Append(@, resp)
        ]

    /\ UNCHANGED active_conns
    /\ UNCHANGED data
    /\ UNCHANGED <<db, last_seq, failed_replicas>>
    /\ UNCHANGED node_vars
    /\ UNCHANGED aux_vars

-------------------------------------------------------------------------------

node_config_change_set(n) ==
    LET
        filter_fn(d) ==
            /\ node_config[n][d] # nil
            /\ ~node_config[n][d].deleted
    IN
        {d \in Dataset: filter_fn(d)}

NewConn(n) ==
    LET
        connect_req == [
            type |-> "Connect",
            node |-> n,
            current |-> node_config_change_set(n)
        ]

        new_conn == [
            send |-> <<connect_req>>,
            recv |-> <<>>,
            closed |-> FALSE
        ]

        conn == Len(global_conn')
    IN
    /\ node_conn[n] = nil
    /\ global_conn' = Append(global_conn, new_conn)
    /\ node_conn' = [node_conn EXCEPT ![n] = conn]
    /\ UNCHANGED <<node_config, node_last_seq, node_events>>
    /\ UNCHANGED node_pending_jobs
    /\ UNCHANGED node_db
    /\ UNCHANGED core_vars
    /\ UNCHANGED data
    /\ UNCHANGED aux_vars


NodeRecvConnectReply(n) ==
    LET
        conn == node_conn[n]
        resp == global_conn[conn].recv[1]
    IN
    /\ conn # nil
    /\ global_conn[conn].recv # <<>>
    /\ resp.type = "ConnectReply"
    /\ global_conn' = [global_conn EXCEPT ![conn].recv = Tail(@)]
    /\ node_last_seq' = [node_last_seq EXCEPT ![n] = resp.seq]

    /\ UNCHANGED data
    /\ UNCHANGED <<node_config, node_conn, node_db, node_events>>
    /\ UNCHANGED node_pending_jobs
    /\ UNCHANGED core_vars
    /\ UNCHANGED aux_vars


NodeRecvConfig(n) ==
    LET
        conn == node_conn[n]
        resp == global_conn[conn].recv[1]
        d == resp.ds
        primary == resp.primary

        new_config == [
            primary |-> resp.primary,
            runner |-> n,
            replicas |-> resp.replicas,
            deleted |-> FALSE
        ]

        synced_replicas == {s \in Storage: node_db[d][s] # nil}

        pending_jobs ==
            IF node_db[d][primary] # nil
                THEN resp.replicas \ synced_replicas
                ELSE {}
    IN
    /\ node_conn[n] # nil
    /\ global_conn[conn].recv # <<>>
    /\ resp.type = "Config"

    /\ global_conn' = [global_conn EXCEPT ![conn].recv = Tail(@)]
    /\ IF resp.deleted
        THEN
            /\ node_config' = [node_config EXCEPT ![n][d] = nil]
            /\ node_pending_jobs' = [node_pending_jobs EXCEPT ![n][d] = {}]
        ELSE
            /\ node_config' = [node_config EXCEPT ![n][d] = new_config]
            /\ node_pending_jobs' = [node_pending_jobs EXCEPT
                    ![n][d] = @ \union pending_jobs]

    /\ UNCHANGED node_last_seq
    /\ UNCHANGED node_events
    /\ UNCHANGED node_conn
    /\ UNCHANGED node_db
    /\ UNCHANGED data
    /\ UNCHANGED core_vars
    /\ UNCHANGED aux_vars


NodeRecvRetryReplica(n) ==
    LET
        conn == node_conn[n]
        resp == global_conn[conn].recv[1]
        d == resp.ds
        s == resp.storage
    IN
    /\ node_conn[n] # nil
    /\ global_conn[conn].recv # <<>>
    /\ resp.type = "RetryReplica"

    /\ global_conn' = [global_conn EXCEPT ![conn].recv = Tail(@)]
    /\ IF node_config[n][d] = nil
        THEN UNCHANGED node_pending_jobs
        ELSE node_pending_jobs' = [node_pending_jobs EXCEPT
                ![n][d] = @ \union {s}]

    /\ UNCHANGED node_events
    /\ UNCHANGED <<node_conn, node_db, node_config, node_last_seq>>
    /\ UNCHANGED data
    /\ UNCHANGED core_vars
    /\ UNCHANGED aux_vars


NodeClearClosedConn(n) ==
    LET
        conn == node_conn[n]
    IN
    /\ node_conn[n] # nil
    /\ global_conn[conn].closed
    /\ node_conn' = [node_conn EXCEPT ![n] = nil]
    /\ node_last_seq' = [node_last_seq EXCEPT ![n] = nil]

    /\ UNCHANGED <<node_config, node_events, node_pending_jobs>>
    /\ UNCHANGED node_db
    /\ UNCHANGED global_conn
    /\ UNCHANGED data
    /\ UNCHANGED core_vars
    /\ UNCHANGED aux_vars


insert_event_new_entry(d, n, s, new_val) ==
    LET
        new_entry == [
            type |-> "NewEntry",
            seq |-> 31 + Len(node_events[n]),
            ds |-> d,
            storage |-> s,
            value |-> node_db'[d][s]
        ]
    IN
    /\ node_db' = [node_db EXCEPT ![d][s] = new_val]
    /\ node_events' = [node_events EXCEPT ![n] = Append(@, new_entry)]


insert_event_failed_new_entry(d, n, s) ==
    LET
        ev == [
            type |-> "NewEntryFailed",
            seq |-> 31 + Len(node_events[n]),
            ds |-> d,
            storage |-> s
        ]
    IN
    /\ node_events' = [node_events EXCEPT ![n] = Append(@, ev)]
    /\ UNCHANGED node_db


NodeUpdateLocalDB(d, n) ==
    LET
        conf == node_config[n][d]
        s == conf.primary
        conn == node_conn[n]

        new_entry == [
            type |-> "NewEntry",
            seq |-> 31 + Len(node_events[n]),
            ds |-> d,
            storage |-> s,
            value |-> data[d][s]
        ]
    IN
    /\ conf # nil
    /\ data[d][s] # node_db[d][s]

    /\ insert_event_new_entry(d, n, s, data[d][s])
    /\ node_pending_jobs' = [node_pending_jobs EXCEPT
            ![n][d] = @ \union conf.replicas]

    /\ UNCHANGED global_conn
    /\ UNCHANGED data
    /\ UNCHANGED <<node_config, node_conn, node_last_seq>>
    /\ UNCHANGED core_vars
    /\ UNCHANGED aux_vars


allowToPushNewEntry(n) ==
    LET
        conn == node_conn[n]
        len == Len(node_events[n])
    IN
    /\ conn # nil
    /\ node_last_seq[n] # nil
    /\ node_last_seq[n] - 30 < len

NodePushNewEntry(n) ==
    LET
        conn == node_conn[n]
        offset == node_last_seq'[n] - 30

        ev == node_events[n][offset]
    IN
    /\ allowToPushNewEntry(n)
    /\ ~global_conn[conn].closed

    /\ node_last_seq' = [node_last_seq EXCEPT ![n] = @ + 1]
    /\ global_conn' = [global_conn EXCEPT ![conn].send = Append(@, ev)]

    /\ UNCHANGED node_events
    /\ UNCHANGED node_pending_jobs
    /\ UNCHANGED data
    /\ UNCHANGED <<node_config, node_conn, node_db>>
    /\ UNCHANGED core_vars
    /\ UNCHANGED aux_vars


NodeHandlePendingJob(d, n, s) ==
    LET
        conf == node_config[n][d]
        primary == conf.primary

        when_normal ==
            /\ data' = [data EXCEPT ![d][s] = data[d][primary]]
            /\ insert_event_new_entry(d, n, s, node_db[d][primary])
            /\ UNCHANGED num_sync_failed

        when_failed ==
            /\ num_sync_failed < max_sync_failed
            /\ num_sync_failed' = num_sync_failed + 1
            /\ UNCHANGED data
            /\ insert_event_failed_new_entry(d, n, s)
    IN
    /\ s \in node_pending_jobs[n][d]

    /\ node_pending_jobs' = [node_pending_jobs EXCEPT ![n][d] = @ \ {s}]
    /\ \/ when_normal
       \/ when_failed

    /\ UNCHANGED <<node_conn, node_config, node_last_seq>>
    /\ UNCHANGED global_conn
    /\ UNCHANGED core_vars
    /\ UNCHANGED <<dataset_sort_order, next_value, num_close_conn, stop_delete>>

-------------------------------------------------------------------------------

ConnectionClose ==
    \E conn \in ConnAddr:
        /\ num_close_conn < max_close_conn
        /\ num_close_conn' = num_close_conn + 1
        /\ ~global_conn[conn].closed
        /\ global_conn' = [global_conn EXCEPT
                ![conn].closed = TRUE,
                ![conn].send = <<>>,
                ![conn].recv = <<>>
            ]
        /\ UNCHANGED data
        /\ UNCHANGED node_vars
        /\ UNCHANGED core_vars
        /\ UNCHANGED dataset_sort_order
        /\ UNCHANGED num_sync_failed
        /\ UNCHANGED next_value
        /\ UNCHANGED stop_delete


EnableStopDelete ==
    /\ ~stop_delete
    /\ stop_delete' = TRUE
    /\ UNCHANGED global_conn
    /\ UNCHANGED num_close_conn
    /\ UNCHANGED dataset_sort_order
    /\ UNCHANGED num_sync_failed
    /\ UNCHANGED data
    /\ UNCHANGED next_value
    /\ UNCHANGED node_vars
    /\ UNCHANGED core_vars

-------------------------------------------------------------------------------

UpdateDiskData(d, s) ==
    /\ next_value < max_value
    /\ next_value' = next_value + 1
    /\ config[d] # nil
    /\ config[d].primary = s

    /\ data' = [data EXCEPT ![d][s] = next_value']

    /\ UNCHANGED global_conn
    /\ UNCHANGED num_close_conn
    /\ UNCHANGED dataset_sort_order
    /\ UNCHANGED num_sync_failed
    /\ UNCHANGED core_vars
    /\ UNCHANGED node_vars
    /\ UNCHANGED stop_delete

-------------------------------------------------------------------------------


stopCondNode(n) ==
    LET
        conn == node_conn[n]
    IN
    /\ server_node_info[n] # nil =>
        /\ server_node_info[n].chan.data = <<>>
        /\ server_node_info[n].chan.status = "Empty"
    /\ node_conn[n] # nil =>
        /\ ~global_conn[conn].closed
        /\ global_conn[conn].send = <<>>
        /\ global_conn[conn].recv = <<>>
    /\ \A d \in Dataset:
        /\ node_pending_jobs[n][d] = {}
        /\ failed_replicas[d] = {}

StopCond ==
    LET
        dataset_cond(d) ==
            /\ config[d] # nil
            /\ ~config[d].deleted
    IN
    /\ \A n \in Node: stopCondNode(n)
    /\ \A d \in Dataset:
        dataset_cond(d) => node_db[d] = data[d]

TerminateCond ==
    /\ StopCond
    /\ num_close_conn = max_close_conn
    /\ next_value = max_value

Terminated ==
    /\ TerminateCond
    /\ UNCHANGED vars


Next ==
    \/ \E d \in Dataset, n \in Node, s \in Storage:
        \/ SetupPrimaryConfig(d, n, s)
        \/ NodeHandlePendingJob(d, n, s)
    \/ \E n \in Node:
        \/ NewConn(n)
        \/ NodeRecvConnectReply(n)
        \/ NodeRecvConfig(n)
        \/ NodeRecvRetryReplica(n)
        \/ NodeClearClosedConn(n)
        \/ NodePushNewEntry(n)
    \/ AcceptConn
    \/ HandleConnect
    \/ \E n \in Node:
        \/ ConsumeChan(n)
        \/ HandleNewEntry(n)
        \/ HandleNewEntryFailed(n)
    \/ \E d \in Dataset:
        \/ DeleteConfig(d)
    \/ \E d \in Dataset, s \in Storage:
        \/ AddReplicaConfig(d, s)
        \/ UpdateDiskData(d, s)
        \/ RetryFailedReplica(d, s)
    \/ \E d \in Dataset, n \in Node:
        \/ NodeUpdateLocalDB(d, n)
    \/ ConnectionClose
    \/ EnableStopDelete
    \/ Terminated

Spec == Init /\ [][Next]_vars

FairSpec == Spec /\ WF_vars(Next)

-------------------------------------------------------------------------------

AlwaysTerminate == <> TerminateCond


NodeConfigMatchServerConfig ==
    LET
        pre_cond(n)==
            /\ node_conn[n] # nil
            /\ stopCondNode(n)

        cond_for_ds(d, n) ==
            LET
                config_with_runner ==
                    /\ config[d] # nil
                    /\ config[d].runner = n
            IN
                config_with_runner =>
                    \/ node_config[n][d] = config[d]
                    \/ /\ node_config[n][d] = nil
                       /\ config[d].deleted

        cond(n) ==
            \A d \in Dataset: cond_for_ds(d, n)
    IN
        \A n \in Node: pre_cond(n) => cond(n)


DataMatchDB ==
    LET
        pre_cond(d) ==
            LET
                n == config[d].runner
            IN
            /\ config[d] # nil
            /\ stopCondNode(n)
            /\ node_config[n][d] # nil
            /\ node_db[d] = data[d]
            /\ node_conn[n] # nil
            /\ ~allowToPushNewEntry(n)
    IN
    \A d \in Dataset:
        pre_cond(d) => data[d] = db[d]


ChannelInv ==
    \A n \in Node:
        LET
            ch == server_node_info[n].chan
        IN
        \/ /\ ch.status = "Nil"
           /\ ch.data = <<>>
        \/ /\ ch.status = "Empty"
           /\ ch.data = <<>>
        \/ /\ ch.status = "Ready"
           /\ Len(ch.data) = 1


ClosedConnInv ==
    \A conn \in ConnAddr:
        global_conn[conn].closed =>
            /\ global_conn[conn].send = <<>>
            /\ global_conn[conn].recv = <<>>


ChangeListShouldNotContainDelete ==
    \A n \in Node: \A i \in DOMAIN config_change_list(n):
        LET d == config_change_list(n)[i] IN
            config[d] # nil => ~config[d].deleted


ServerNodeInfoPendingListNonDuplicated ==
    \A n \in Node:
        seq_not_duplicated(server_node_info[n].pending)


ServerNodeInfoPendingListMatchPendingSet ==
    \A n \in Node:
        Range(server_node_info[n].pending) = server_node_info[n].pending_set


NodeLastSeqInv ==
    \A n \in Node:
        node_last_seq[n] # nil => node_conn[n] # nil


node_get_max_seq(n) ==
    node_events[n][Len(node_events[n])].seq

DiskReplicaMustExisted ==
    \A d \in Dataset:
        LET
            n == config[d].runner
            primary == config[d].primary

            pre_cond ==
                /\ config[d] # nil
                /\ stopCondNode(n)
                /\ node_config[n][d] # nil
                /\ node_conn[n] # nil
                /\ node_db[d][primary] # nil
                /\ data[d][primary] = node_db[d][primary]
                /\ node_last_seq[n] = node_get_max_seq(n)

            cond ==
                /\ \A s \in config[d].replicas:
                        data[d][s] = data[d][primary]
        IN
            pre_cond => cond


NodePendingJobInv ==
    \A d \in Dataset:
        LET
            primary == config[d].primary
            n == config[d].runner

            first_cond ==
                /\ node_pending_jobs[n][d] \subseteq config[d].replicas
                /\ node_pending_jobs[n][d] # {} => node_db[d][primary] # nil

            second_cond ==
                node_config[n][d] = nil =>
                    node_pending_jobs[n][d] = {}
        IN
            config[d] # nil =>
                /\ first_cond
                /\ second_cond


NodeEventsMustNotDuplicated ==
    \A n \in Node:
        LET
            clear_seq(ev) == [ev EXCEPT !.seq = 31]

            list == [
                i \in DOMAIN node_events[n] |->
                    clear_seq(node_events[n][i])]
        IN
            seq_not_duplicated(list)

====

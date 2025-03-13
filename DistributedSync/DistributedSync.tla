------ MODULE DistributedSync ----
EXTENDS TLC, Naturals, Sequences, FiniteSets

CONSTANTS Dataset, Node, Storage, nil, max_close_conn

VARIABLES
    config, active_conns, server_node_info,
    data, global_conn,
    node_conn, node_config, main_pc,
    num_close_conn, dataset_sort_order

core_vars == <<
    config, active_conns, server_node_info
>>

node_vars == <<node_conn, node_config, main_pc>>
aux_vars == <<num_close_conn, dataset_sort_order>>
vars == <<core_vars, data, global_conn, node_vars, aux_vars>>

-------------------------------------------------------------------------------

Range(f) == {f[x]: x \in DOMAIN f}

seq_not_duplicated(f) ==
    Cardinality(Range(f)) = Len(f)

-------------------------------------------------------------------------------

Value == 21..29
NullValue == Value \union {nil}

NullNode == Node \union {nil}

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
    IN
        UNION {connect}

Response == [
    type: {"Config"},
    ds: Dataset,
    primary: Storage,
    deleted: BOOLEAN
]

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
    /\ data \in [Storage -> [Dataset -> NullValue]]
    /\ global_conn \in Seq(Conn)
    /\ node_conn \in [Node -> NullConn]
    /\ node_config \in [Node -> [Dataset -> NullConfig]]
    /\ main_pc \in [Node -> {"Init"}]
    /\ num_close_conn \in 0..max_close_conn
    /\ dataset_sort_order \in Seq(Dataset)
    /\ Range(dataset_sort_order) = Dataset

Init ==
    /\ config = [d \in Dataset |-> nil]
    /\ server_node_info = [n \in Node |-> init_server_node_info]
    /\ active_conns = {}
    /\ data = [s \in Storage |-> [d \in Dataset |-> nil]]
    /\ global_conn = <<>>
    /\ node_conn = [n \in Node |-> nil]
    /\ node_config = [n \in Node |-> [d \in Dataset |-> nil]]
    /\ main_pc = [n \in Node |-> "Init"]
    /\ num_close_conn = 0
    /\ dataset_sort_order \in [1..num_dataset -> Dataset]
    /\ Range(dataset_sort_order) = Dataset

-------------------------------------------------------------------------------

new_config_resp(d) == [
    type |-> "Config",
    ds |-> d,
    primary |-> config'[d].primary,
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
    /\ UNCHANGED active_conns
    /\ UNCHANGED data
    /\ UNCHANGED node_vars
    /\ UNCHANGED global_conn
    /\ UNCHANGED aux_vars


DeleteConfig(d) ==
    LET
        n == config[d].runner

        filter_fn(x) == x # d

        remove_deleted(list) ==
            SelectSeq(list, filter_fn)
    IN
    /\ config[d] # nil
    /\ ~config[d].deleted
    /\ config' = [config EXCEPT ![d].deleted = TRUE]
    /\ updateConfigPushToChan(d, config[d].runner)
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
        /\ UNCHANGED server_node_info
        /\ UNCHANGED config
        /\ UNCHANGED data
        /\ UNCHANGED node_vars
        /\ UNCHANGED aux_vars


doHandleConnect(conn) ==
    LET
        req == global_conn[conn].send[1]
        n == req.node

        filter_fn(d) ==
            \/ config_is_active(d, n)
            \/ d \in req.current

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
    /\ global_conn' = [global_conn EXCEPT ![conn].send = Tail(@)]

    /\ UNCHANGED config
    /\ IF pending_list = <<>>
        THEN when_pending_empty
        ELSE when_pending_non_empty

    /\ UNCHANGED active_conns
    /\ UNCHANGED data
    /\ UNCHANGED node_vars
    /\ UNCHANGED aux_vars

HandleConnect ==
    \E conn \in ConnAddr: doHandleConnect(conn)


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
    /\ UNCHANGED node_config
    /\ UNCHANGED core_vars
    /\ UNCHANGED data
    /\ UNCHANGED main_pc
    /\ UNCHANGED aux_vars


RecvConfig(n) ==
    LET
        conn == node_conn[n]
        resp == global_conn[conn].recv[1]
        d == resp.ds

        new_config == [
            primary |-> resp.primary,
            runner |-> n,
            replicas |-> {},
            deleted |-> resp.deleted
        ]
    IN
    /\ node_conn[n] # nil
    /\ global_conn[conn].recv # <<>>
    /\ resp.type = "Config"
    /\ global_conn' = [global_conn EXCEPT ![conn].recv = Tail(@)]

    /\ node_config' = [node_config EXCEPT ![n][d] = new_config]
    /\ UNCHANGED node_conn
    /\ UNCHANGED main_pc
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

    /\ UNCHANGED main_pc
    /\ UNCHANGED node_config
    /\ UNCHANGED global_conn
    /\ UNCHANGED data
    /\ UNCHANGED core_vars
    /\ UNCHANGED aux_vars

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

StopCond ==
    /\ \A n \in Node: stopCondNode(n)

TerminateCond ==
    /\ StopCond
    /\ num_close_conn = max_close_conn

Terminated ==
    /\ TerminateCond
    /\ UNCHANGED vars


Next ==
    \/ \E d \in Dataset, n \in Node, s \in Storage:
        \/ SetupPrimaryConfig(d, n, s)
    \/ \E n \in Node:
        \/ NewConn(n)
        \/ RecvConfig(n)
        \/ NodeClearClosedConn(n)
    \/ AcceptConn
    \/ HandleConnect
    \/ \E n \in Node:
        \/ ConsumeChan(n)
    \/ \E d \in Dataset:
        \/ DeleteConfig(d)
    \/ ConnectionClose
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

====

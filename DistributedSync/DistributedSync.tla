------ MODULE DistributedSync ----
EXTENDS TLC, Naturals, Sequences

CONSTANTS Dataset, Node, Storage, nil, max_close_conn

VARIABLES
    config, change_list, active_conns, server_node_info,
    data, global_conn,
    node_conn, node_config, main_pc,
    num_close_conn

core_vars == <<
    config, change_list, active_conns, server_node_info
>>

node_vars == <<node_conn, node_config, main_pc>>
aux_vars == <<num_close_conn>>
vars == <<core_vars, data, global_conn, node_vars, aux_vars>>

-------------------------------------------------------------------------------

Range(f) == {f[x]: x \in DOMAIN f}

IsMapOf(m, K, V) ==
    /\ DOMAIN m \subseteq K
    /\ Range(m) \subseteq V

MapPut(m, k, v) ==
    LET
        new_dom == DOMAIN m \union {k}
    IN
        [x \in new_dom |-> IF x = k THEN v ELSE m[x]]

ASSUME MapPut(<<>>, 1, 3) = <<3>>
ASSUME MapPut(<<5>>, 1, 4) = <<4>>
ASSUME MapPut(<<5>>, 2, 6) = <<5, 6>>

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
            node: Node
        ]
    IN
        UNION {connect}

Response == [
    type: {"Config"},
    ds: Dataset,
    primary: Storage
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
    pending: Seq(Dataset)
]

nil_chan == [
    status |-> "Nil",
    data |-> <<>>
]

init_server_node_info == [
    conn |-> nil,
    chan |-> nil_chan,
    pending |-> <<>>
]

-------------------------------------------------------------------------------

TypeOK ==
    /\ config \in [Dataset -> NullConfig]
    /\ change_list \in [Node -> Seq(Dataset)]
    /\ server_node_info \in [Node -> ServerNodeInfo]
    /\ active_conns \subseteq ConnAddr
    /\ data \in [Storage -> [Dataset -> NullValue]]
    /\ global_conn \in Seq(Conn)
    /\ node_conn \in [Node -> NullConn]
    /\ node_config \in [Node -> [Dataset -> NullConfig]]
    /\ main_pc \in [Node -> {"Init"}]
    /\ num_close_conn \in 0..max_close_conn

Init ==
    /\ config = [d \in Dataset |-> nil]
    /\ change_list = [n \in Node |-> <<>>]
    /\ server_node_info = [n \in Node |-> init_server_node_info]
    /\ active_conns = {}
    /\ data = [s \in Storage |-> [d \in Dataset |-> nil]]
    /\ global_conn = <<>>
    /\ node_conn = [n \in Node |-> nil]
    /\ node_config = [n \in Node |-> [d \in Dataset |-> nil]]
    /\ main_pc = [n \in Node |-> "Init"]
    /\ num_close_conn = 0

-------------------------------------------------------------------------------

new_config_resp(d) == [
    type |-> "Config",
    ds |-> d,
    primary |-> config'[d].primary
]

new_ready_chan(resp) == [
    status |-> "Ready",
    data |-> <<resp>>
]

SetupPrimaryConfig(d, n, s) ==
    LET
        new_config == [
            primary |-> s,
            runner |-> n,
            replicas |-> {},
            deleted |-> FALSE
        ]

        ch == server_node_info[n].chan

        when_chan_nil ==
            /\ server_node_info' = [server_node_info EXCEPT
                    ![n].pending = Append(@, d) \* TODO not append when not needed
                ]

        when_chan_not_nil ==
            /\ server_node_info' = [server_node_info EXCEPT
                    ![n].chan = new_ready_chan(new_config_resp(d))
                ]
    IN
    /\ config[d] = nil
    /\ config' = [config EXCEPT ![d] = new_config]
    /\ change_list' = [change_list EXCEPT ![n] = Append(@, d)]
    /\ IF ch.status \in {"Nil", "Ready"}
        THEN when_chan_nil
        ELSE when_chan_not_nil
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
    /\ change_list' = [change_list EXCEPT ![n] = remove_deleted(@)]
    /\ UNCHANGED server_node_info
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
        /\ UNCHANGED change_list
        /\ UNCHANGED data
        /\ UNCHANGED node_vars
        /\ UNCHANGED aux_vars


doHandleConnect(conn) ==
    LET
        req == global_conn[conn].send[1]
        n == req.node

        pending_list == change_list[n]
        pending_ds == pending_list[1]

        when_pending_empty ==
            /\ server_node_info' = [server_node_info EXCEPT
                    ![n].conn = conn,
                    ![n].chan = new_empty_chan
                ]

        when_pending_non_empty ==
            /\ server_node_info' = [server_node_info EXCEPT
                    ![n].conn = conn,
                    ![n].pending = Tail(pending_list),
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

    /\ UNCHANGED change_list
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

        when_non_empty ==
            /\ server_node_info' = [server_node_info EXCEPT
                    ![n].chan = pushed_ch,
                    ![n].pending = Tail(@)
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

    /\ UNCHANGED change_list
    /\ UNCHANGED active_conns
    /\ UNCHANGED data
    /\ UNCHANGED node_vars
    /\ UNCHANGED aux_vars

-------------------------------------------------------------------------------

NewConn(n) ==
    LET
        connect_req == [
            type |-> "Connect",
            node |-> n
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
            deleted |-> FALSE
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

-------------------------------------------------------------------------------

NodeConfigMatchServerConfig ==
    LET
        pre_cond(n)==
            /\ node_conn[n] # nil
            /\ stopCondNode(n)

        cond(n) ==
            \A d \in Dataset:
                LET
                    config_with_runner ==
                        /\ config[d] # nil
                        /\ config[d].runner = n
                IN
                    config_with_runner => node_config[n][d] = config[d]
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
    \A n \in Node: \A i \in DOMAIN change_list[n]:
        LET d == change_list[n][i] IN
            config[d] # nil => ~config[d].deleted


====

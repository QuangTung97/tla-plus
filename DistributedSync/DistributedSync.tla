------ MODULE DistributedSync ----
EXTENDS TLC, Naturals, Sequences

CONSTANTS Dataset, Node, Storage, nil

VARIABLES
    config, active_conns, server_node_info,
    data, global_conn,
    node_conn, node_config, main_pc

core_vars == <<
    config, active_conns, server_node_info
>>

node_vars == <<
    node_conn, node_config, main_pc
>>

vars == <<core_vars, data, global_conn, node_vars>>

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
    replicas: SUBSET Storage
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
    status: {"Empty", "Ready"},
    data: Seq(Response)
]

init_chan == [
    status |-> "Empty",
    data |-> <<>>
]

ServerNodeInfo == [
    conn: ConnAddr,
    chan: Channel
]

-------------------------------------------------------------------------------

TypeOK ==
    /\ config \in [Dataset -> NullConfig]
    /\ server_node_info \in [Node -> (ServerNodeInfo \union {nil})]
    /\ active_conns \subseteq ConnAddr
    /\ data \in [Storage -> [Dataset -> NullValue]]
    /\ global_conn \in Seq(Conn)
    /\ node_conn \in [Node -> NullConn]
    /\ node_config \in [Node -> [Dataset -> NullConfig]]
    /\ main_pc \in [Node -> {"Init"}]

Init ==
    /\ config = [d \in Dataset |-> nil]
    /\ server_node_info = [n \in Node |-> nil]
    /\ active_conns = {}
    /\ data = [s \in Storage |-> [d \in Dataset |-> nil]]
    /\ global_conn = <<>>
    /\ node_conn = [n \in Node |-> nil]
    /\ node_config = [n \in Node |-> [d \in Dataset |-> nil]]
    /\ main_pc = [n \in Node |-> "Init"]

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
            replicas |-> {}
        ]

        when_info_nil ==
            /\ UNCHANGED server_node_info

        when_info_not_nil ==
            /\ server_node_info' = [server_node_info EXCEPT
                    ![n].chan = new_ready_chan(new_config_resp(d))
                ]
    IN
    /\ config[d] = nil
    /\ config' = [config EXCEPT ![d] = new_config]
    /\ IF server_node_info[n] = nil
        THEN when_info_nil
        ELSE when_info_not_nil
    /\ UNCHANGED active_conns
    /\ UNCHANGED data
    /\ UNCHANGED node_vars
    /\ UNCHANGED global_conn


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


doHandleConnect(conn) ==
    LET
        req == global_conn[conn].send[1]

        new_empty_info == [
            conn |-> conn,
            chan |-> init_chan
        ]

        config_is_valid(d) ==
            /\ config[d] # nil
            /\ config[d].runner = req.node

        exist_config == \E d \in Dataset: config_is_valid(d)


        new_ready_info(d) == [
            conn |-> conn,
            chan |-> new_ready_chan(new_config_resp(d))
        ]

        when_non_empty(d) ==
            /\ config_is_valid(d)
            /\ server_node_info' = [server_node_info EXCEPT
                    ![req.node] = new_ready_info(d)]

        when_empty_config ==
            /\ server_node_info' = [server_node_info EXCEPT
                    ![req.node] = new_empty_info]
    IN
    /\ conn \in active_conns
    /\ global_conn[conn].send # <<>>
    /\ global_conn' = [global_conn EXCEPT ![conn].send = Tail(@)]

    /\ UNCHANGED config
    /\ IF exist_config
        THEN \E d \in Dataset: when_non_empty(d)
        ELSE when_empty_config

    /\ UNCHANGED active_conns
    /\ UNCHANGED data
    /\ UNCHANGED node_vars

HandleConnect ==
    \E conn \in ConnAddr: doHandleConnect(conn)


ConsumeChan(n) ==
    LET
        resp == server_node_info[n].chan.data[1]

        conn == server_node_info[n].conn
    IN
    /\ server_node_info[n] # nil
    /\ server_node_info[n].chan.status = "Ready"
    /\ server_node_info' = [server_node_info EXCEPT
            ![n].chan.data = Tail(@),
            ![n].chan.status = "Empty"
        ]
    /\ global_conn' = [global_conn EXCEPT ![conn].recv = Append(@, resp)]
    /\ UNCHANGED config
    /\ UNCHANGED active_conns
    /\ UNCHANGED data
    /\ UNCHANGED node_vars

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


RecvConfig(n) ==
    LET
        conn == node_conn[n]
        resp == global_conn[conn].recv[1]
        d == resp.ds

        new_config == [
            primary |-> resp.primary,
            runner |-> n,
            replicas |-> {}
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

-------------------------------------------------------------------------------


stopCondNode(n) ==
    LET
        conn == node_conn[n]
    IN
    /\ server_node_info[n] # nil =>
        /\ server_node_info[n].chan.data = <<>>
        /\ server_node_info[n].chan.status = "Empty"
    /\ node_conn[n] # nil =>
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
    \/ AcceptConn
    \/ HandleConnect
    \/ \E n \in Node:
        \/ ConsumeChan(n)
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

====

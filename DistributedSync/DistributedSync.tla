------ MODULE DistributedSync ----
EXTENDS TLC, Naturals, Sequences

CONSTANTS Dataset, Node, Storage, nil

VARIABLES config, active_conns,
    data, global_conn,
    node_conn, main_pc

core_vars == <<
    config, active_conns
>>

node_vars == <<
    node_conn, main_pc
>>

vars == <<core_vars, data, global_conn, node_vars>>

-------------------------------------------------------------------------------

Value == 21..29
NullValue == Value \union {nil}

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

-------------------------------------------------------------------------------

TypeOK ==
    /\ config \in [Dataset -> NullConfig]
    /\ active_conns \subseteq ConnAddr
    /\ data \in [Storage -> [Dataset -> NullValue]]
    /\ global_conn \in Seq(Conn)
    /\ node_conn \in [Node -> NullConn]
    /\ main_pc \in [Node -> {"Init"}]

Init ==
    /\ config = [d \in Dataset |-> nil]
    /\ active_conns = {}
    /\ data = [s \in Storage |-> [d \in Dataset |-> nil]]
    /\ global_conn = <<>>
    /\ node_conn = [n \in Node |-> nil]
    /\ main_pc = [n \in Node |-> "Init"]

-------------------------------------------------------------------------------

SetupPrimaryConfig(d, n, s) ==
    LET
        new_config == [
            primary |-> s,
            runner |-> n,
            replicas |-> {}
        ]
    IN
    /\ config[d] = nil
    /\ config' = [config EXCEPT ![d] = new_config]
    /\ UNCHANGED active_conns
    /\ UNCHANGED data
    /\ UNCHANGED node_vars
    /\ UNCHANGED global_conn


AcceptConn ==
    \E conn \in ConnAddr:
        /\ conn \notin active_conns
        /\ ~global_conn[conn].closed
        /\ active_conns' = active_conns \union {conn}
        /\ UNCHANGED global_conn
        /\ UNCHANGED config
        /\ UNCHANGED data
        /\ UNCHANGED node_vars


HandleConnect ==
    \E conn \in ConnAddr:
        LET
            req == global_conn[conn].send[1]
        IN
        /\ conn \in active_conns
        /\ global_conn[conn].send # <<>>
        /\ global_conn' = [global_conn EXCEPT ![conn].send = Tail(@)]

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
    /\ UNCHANGED core_vars
    /\ UNCHANGED data
    /\ UNCHANGED main_pc

-------------------------------------------------------------------------------

TerminateCond ==
    /\ TRUE

Terminated ==
    /\ TerminateCond
    /\ UNCHANGED vars


Next ==
    \/ \E d \in Dataset, n \in Node, s \in Storage:
        \/ SetupPrimaryConfig(d, n, s)
    \/ \E n \in Node:
        \/ NewConn(n)
    \/ AcceptConn
    \/ HandleConnect
    \/ Terminated

Spec == Init /\ [][Next]_vars

====

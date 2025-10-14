------ MODULE PandoraScheduler ----
EXTENDS TLC, Sequences, Naturals, FiniteSets

CONSTANTS Node, nil, max_active

VARIABLES
    global_conns,
    pc, local_conn,
    conn_node,
    active_nodes, pause_nodes

vars == <<
    global_conns,
    pc, local_conn,
    conn_node,
    active_nodes, pause_nodes
>>

-----------------------------------------------------------

NullNode == Node \union {nil}

Request ==
    LET
        init_req == [
            type: {"Init"},
            node: Node
        ]

        finish_req == [
            type: {"Finish"}
        ]
    IN
        UNION {init_req, finish_req}

Response == [
    type: {"Start"}
]

ConnObj == [
    send: Seq(Request),
    recv: Seq(Response),
    closed: BOOLEAN
]

Conn == DOMAIN global_conns
NullConn == Conn \union {nil}

PC == {"Init", "SendInit", "WaitScheduler", "Running", "Terminated"}

-----------------------------------------------------------

TypeOK ==
    /\ global_conns \in Seq(ConnObj)
    /\ pc \in [Node -> PC]
    /\ local_conn \in [Node -> NullConn]
    /\ conn_node \in [Conn -> NullNode]
    /\ active_nodes \subseteq Node
    /\ pause_nodes \subseteq Node
    /\ active_nodes \intersect pause_nodes = {}

Init ==
    /\ global_conns = <<>>
    /\ pc = [n \in Node |-> "Init"]
    /\ local_conn = [n \in Node |-> nil]
    /\ conn_node = <<>>
    /\ active_nodes = {}
    /\ pause_nodes = {}

-----------------------------------------------------------

goto(n, l) ==
    pc' = [pc EXCEPT ![n] = l]

NewConn(n) ==
    LET
        new_conn == [
            send |-> <<>>,
            recv |-> <<>>,
            closed |-> FALSE
        ]
        conn == Len(global_conns')
    IN
    /\ pc[n] = "Init"
    /\ goto(n, "SendInit")
    /\ global_conns' = Append(global_conns, new_conn)
    /\ conn_node' = Append(conn_node, nil)
    /\ local_conn' = [local_conn EXCEPT ![n] = conn]
    /\ UNCHANGED <<active_nodes, pause_nodes>>

---------------------------------

nodeUnchanged ==
    /\ UNCHANGED conn_node
    /\ UNCHANGED active_nodes
    /\ UNCHANGED pause_nodes

SendInit(n) ==
    LET
        conn == local_conn[n]
        req == [
            type |-> "Init",
            node |-> n
        ]

        when_normal ==
            /\ ~global_conns[conn].closed
            /\ goto(n, "WaitScheduler")
            /\ global_conns' = [global_conns EXCEPT
                    ![conn].send = Append(@, req)
                ]

        when_closed ==
            /\ global_conns[conn].closed
            /\ goto(n, "Terminated")
            /\ UNCHANGED global_conns
    IN
    /\ pc[n] = "SendInit"
    /\ \/ when_normal
       \/ when_closed

    /\ UNCHANGED local_conn
    /\ nodeUnchanged

---------------------------------

WaitScheduler(n) ==
    LET
        conn == local_conn[n]
        recv == global_conns[conn].recv

        when_normal ==
            /\ recv # <<>>
            /\ goto(n, "Running")
            /\ global_conns' = [global_conns EXCEPT ![conn].recv = Tail(@)]

        when_closed ==
            /\ global_conns[conn].closed
            /\ goto(n, "Terminated")
            /\ UNCHANGED global_conns
    IN
    /\ pc[n] = "WaitScheduler"
    /\ \/ when_normal
       \/ when_closed

    /\ UNCHANGED local_conn
    /\ nodeUnchanged

---------------------------------

Running(n) ==
    LET
        conn == local_conn[n]
        req == [
            type |-> "Finish"
        ]
    IN
    /\ pc[n] = "Running"
    /\ goto(n, "Terminated")
    /\ IF global_conns[conn].closed
        THEN UNCHANGED global_conns
        ELSE global_conns' = [global_conns EXCEPT
                ![conn].send = Append(@, req)
            ]

    /\ UNCHANGED local_conn
    /\ nodeUnchanged

-----------------------------------------------------------

serverUnchanged ==
    /\ UNCHANGED <<pc, local_conn>>

serverConnHasData(conn) ==
    /\ ~global_conns[conn].closed
    /\ global_conns[conn].send # <<>>

serverConnClosed(conn) ==
    /\ global_conns[conn].closed

doServerRecvInit(conn) ==
    LET
        remove_send == [global_conns EXCEPT ![conn].send = Tail(@)]
        req == global_conns[conn].send[1]

        resp == [
            type |-> "Start"
        ]
        send_resp == [remove_send EXCEPT ![conn].recv = Append(@, resp)]

        when_normal ==
            /\ global_conns' = send_resp
            /\ active_nodes' = active_nodes \union {req.node}
            /\ UNCHANGED pause_nodes

        when_pause ==
            /\ global_conns' = remove_send
            /\ pause_nodes' = pause_nodes \union {req.node}
            /\ UNCHANGED active_nodes
    IN
    /\ serverConnHasData(conn)
    /\ req.type = "Init"

    /\ conn_node' = [conn_node EXCEPT ![conn] = req.node]
    /\ IF Cardinality(active_nodes) < max_active
        THEN when_normal
        ELSE when_pause

    /\ serverUnchanged

ServerRecvInit ==
    \E conn \in Conn:
        doServerRecvInit(conn)

---------------------------------

doServerRecvFinish(conn) ==
    LET
        req == global_conns[conn].send[1]
        n == conn_node[conn]

        remove_send == [global_conns EXCEPT ![conn].send = Tail(@)]
        active_removed == active_nodes \ {n}

        when_no_pause ==
            /\ global_conns' = remove_send
            /\ active_nodes' = active_removed
            /\ UNCHANGED pause_nodes

        resp == [
            type |-> "Start"
        ]

        conn_of_node(n1) == CHOOSE c1 \in Conn: conn_node[c1] = n1

        send_resp(n1) ==
            LET
                c1 == conn_of_node(n1)
                is_closed == remove_send[c1].closed

                do_send == [remove_send EXCEPT
                    ![c1].recv = Append(@, resp)
                ]
            IN
                IF is_closed
                    THEN remove_send
                    ELSE do_send

        when_with_pause ==
            \E n1 \in pause_nodes:
                /\ pause_nodes' = pause_nodes \ {n1}
                /\ active_nodes' = active_removed \union {n1}
                /\ global_conns' = send_resp(n1)
    IN
    /\ serverConnHasData(conn)
    /\ req.type = "Finish"

    /\ conn_node' = [conn_node EXCEPT ![conn] = nil]
    /\ IF pause_nodes = {}
        THEN when_no_pause
        ELSE when_with_pause

    /\ serverUnchanged

ServerRecvFinish ==
    \E conn \in Conn:
        doServerRecvFinish(conn)

---------------------------------

doServerCloseConn(conn) ==
    LET
        n == conn_node[conn]
    IN
    /\ serverConnClosed(conn)

    /\ conn_node[conn] # nil
    /\ conn_node' = [conn_node EXCEPT ![conn] = nil]

    /\ active_nodes' = active_nodes \ {n}
    /\ pause_nodes' = pause_nodes \ {n}

    /\ UNCHANGED global_conns
    /\ serverUnchanged

ServerCloseConn ==
    \E conn \in Conn:
        doServerCloseConn(conn)

---------------------------------

doDisconnectConn(conn) ==
    /\ ~global_conns[conn].closed
    /\ global_conns' = [global_conns EXCEPT
            ![conn].closed = TRUE,
            ![conn].send = <<>>,
            ![conn].recv = <<>>
        ]

    /\ UNCHANGED active_nodes
    /\ UNCHANGED pause_nodes
    /\ UNCHANGED conn_node

    /\ serverUnchanged

DisconnectConn ==
    \E conn \in Conn:
        doDisconnectConn(conn)

-----------------------------------------------------------

TerminateCond ==
    /\ \A n \in Node: pc[n] = "Terminated"
    /\ \A c \in Conn:
        /\ global_conns[c].send = <<>>
        /\ global_conns[c].recv = <<>>
    /\ active_nodes = {}
    /\ pause_nodes = {}
    /\ \A c \in Conn: conn_node[c] = nil

Terminated ==
    /\ TerminateCond
    /\ UNCHANGED vars

Next ==
    \/ \E n \in Node:
        \/ NewConn(n)
        \/ SendInit(n)
        \/ WaitScheduler(n)
        \/ Running(n)
    \/ ServerRecvInit
    \/ ServerRecvFinish
    \/ DisconnectConn
    \/ ServerCloseConn
    \/ Terminated

Spec == Init /\ [][Next]_vars

FairSpec == Spec /\ WF_vars(Next)

-----------------------------------------------------------

AlwaysTerminated == []<>TerminateCond


MaxActiveInv ==
    Cardinality(active_nodes) <= max_active


NodeConnInv ==
    LET
        active_conns == {c \in Conn: conn_node[c] # nil}
    IN
        {conn_node[c]: c \in active_conns} = active_nodes \union pause_nodes

ConnClosedInv ==
    \A c \in Conn:
        global_conns[c].closed =>
            /\ global_conns[c].send = <<>>
            /\ global_conns[c].recv = <<>>

====

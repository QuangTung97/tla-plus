------ MODULE PandoraScheduler ----
EXTENDS TLC, Sequences, Naturals, FiniteSets

CONSTANTS Node, nil, max_active

VARIABLES
    global_conns,
    pc, local_conn,
    server_conns, conn_node,
    active_nodes, pause_nodes

vars == <<
    global_conns,
    pc, local_conn,
    server_conns, conn_node,
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
    recv: Seq(Response)
]

Conn == DOMAIN global_conns
NullConn == Conn \union {nil}

PC == {"Init", "SendInit", "WaitScheduler", "Running", "Terminated"}

-----------------------------------------------------------

TypeOK ==
    /\ global_conns \in Seq(ConnObj)
    /\ pc \in [Node -> PC]
    /\ local_conn \in [Node -> NullConn]
    /\ server_conns \subseteq Conn
    /\ conn_node \in [Conn -> NullNode]
    /\ active_nodes \subseteq Node
    /\ pause_nodes \subseteq Node
    /\ active_nodes \intersect pause_nodes = {}

Init ==
    /\ global_conns = <<>>
    /\ pc = [n \in Node |-> "Init"]
    /\ local_conn = [n \in Node |-> nil]
    /\ server_conns = {}
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
            recv |-> <<>>
        ]
        conn == Len(global_conns')
    IN
    /\ pc[n] = "Init"
    /\ goto(n, "SendInit")
    /\ global_conns' = Append(global_conns, new_conn)
    /\ conn_node' = Append(conn_node, nil)
    /\ server_conns' = server_conns \union {conn}
    /\ local_conn' = [local_conn EXCEPT ![n] = conn]
    /\ UNCHANGED <<active_nodes, pause_nodes>>

---------------------------------

nodeUnchanged ==
    /\ UNCHANGED server_conns
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
    IN
    /\ pc[n] = "SendInit"
    /\ goto(n, "WaitScheduler")
    /\ global_conns' = [global_conns EXCEPT
            ![conn].send = Append(@, req)
        ]

    /\ UNCHANGED local_conn
    /\ nodeUnchanged

---------------------------------

WaitScheduler(n) ==
    LET
        conn == local_conn[n]
        recv == global_conns[conn].recv
    IN
    /\ pc[n] = "WaitScheduler"
    /\ recv # <<>>

    /\ goto(n, "Running")
    /\ global_conns' = [global_conns EXCEPT ![conn].recv = Tail(@)]

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
    /\ global_conns' = [global_conns EXCEPT ![conn].send = Append(@, req)]

    /\ UNCHANGED local_conn
    /\ nodeUnchanged

-----------------------------------------------------------

serverUnchanged ==
    /\ UNCHANGED <<pc, local_conn>>

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
    /\ global_conns[conn].send # <<>>
    /\ req.type = "Init"

    /\ conn_node' = [conn_node EXCEPT ![conn] = req.node]
    /\ IF Cardinality(active_nodes) < max_active
        THEN when_normal
        ELSE when_pause

    /\ UNCHANGED server_conns
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

        send_resp(n1) == [remove_send EXCEPT
                ![conn_of_node(n1)].recv = Append(@, resp)
        ]

        when_with_pause ==
            \E n1 \in pause_nodes:
                /\ pause_nodes' = pause_nodes \ {n1}
                /\ active_nodes' = active_removed \union {n1}
                /\ global_conns' = send_resp(n1)
    IN
    /\ global_conns[conn].send # <<>>
    /\ req.type = "Finish"

    /\ server_conns' = server_conns \ {conn}
    /\ conn_node' = [conn_node EXCEPT ![conn] = nil]
    /\ IF pause_nodes = {}
        THEN when_no_pause
        ELSE when_with_pause

    /\ serverUnchanged

ServerRecvFinish ==
    \E conn \in Conn:
        doServerRecvFinish(conn)

-----------------------------------------------------------

TerminateCond ==
    /\ \A n \in Node: pc[n] = "Terminated"
    /\ \A c \in Conn:
        /\ global_conns[c].send = <<>>
        /\ global_conns[c].recv = <<>>
    /\ server_conns = {}
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

====

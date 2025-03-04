------ MODULE Zookeeper ----
EXTENDS TLC, Sequences, Naturals, FiniteSets

CONSTANTS Group, Ephemeral, Key, Value,
    Client, nil, max_action, max_conn_closed

ASSUME
    /\ Ephemeral \subseteq Group
    /\ IsFiniteSet(Group)

VARIABLES server_log, server_state, active_conns, active_sessions,
    global_conn,
    client_conn, client_main_pc, last_session, last_zxid,
    client_send_pc, client_recv_pc,
    send_queue, recv_map, handle_queue,
    num_action, next_xid, handled_xid, local_xid,
    num_conn_closed

server_vars == <<server_log, server_state, active_conns, active_sessions>>
client_vars == <<
    client_conn, client_main_pc, last_session, last_zxid,
    client_send_pc, client_recv_pc,
    send_queue, recv_map, handle_queue,
    num_action, next_xid, handled_xid, local_xid
>>

aux_vars == <<num_conn_closed>>
vars == <<server_vars, global_conn, client_vars, aux_vars>>

---------------------------------------------------------------------------

Range(f) == {f[x]: x \in DOMAIN f}

IsMapOf(m, D, R) ==
    /\ DOMAIN m \subseteq D
    /\ Range(m) \subseteq R

mapPut(m, k, v) ==
    LET
        new_domain == (DOMAIN m) \union {k}

        updated(x) ==
            IF x = k
                THEN v
                ELSE m[x]
    IN
    [x \in new_domain |-> updated(x)]

ASSUME mapPut(<<3, 4>>, 1, 4) = <<4, 4>>
ASSUME mapPut(<<3, 4>>, 3, 5) = <<3, 4, 5>>

mapDelete(m, k) ==
    LET
        new_domain == (DOMAIN m) \ {k}
    IN
    [x \in new_domain |-> m[x]]

ASSUME mapDelete(<<3, 4, 5>>, 3) = <<3, 4>>


maxOf(S) == CHOOSE x \in S: (\A y \in S: y <= x)

ASSUME maxOf({4, 2, 3}) = 4

---------------------------------------------------------------------------

Zxid == 21..29

NullZxid == Zxid \union {nil}


Session == 11..19

NullSession == Session \union {nil}


LogEntry ==
    LET
        sessionEntry == [
            type: {"NewSession"},
            zxid: Zxid,
            sess: Session
        ]

        putEntry == [
            type: {"Put"},
            zxid: Zxid,
            group: Group,
            key: Key,
            val: Value
        ]
    IN
    sessionEntry \union putEntry


SeqKey == Key \union (Key \X (1..20))

StateInfo == [
    val: Value,
    sess: NullSession \* For Ephemeral ZNodes
]

ServerConnInfo == [
    sess: NullSession
]

Xid == 30..39

SendRequest ==
    LET
        connect_req == [
            type: {"Connect"},
            sess: NullSession,
            seen_zxid: NullZxid
        ]

        create_req == [
            type: {"Create"},
            xid: Xid,
            group: Group,
            key: Key,
            val: Value
        ]
    IN
        connect_req \union create_req

RecvRequest ==
    LET
        connect_resp == [type: {"ConnectReply"}, sess: NullSession]

        create_resp == [
            type: {"CreateReply"},
            xid: Xid,
            zxid: Zxid,
            key: SeqKey
        ]
    IN
        connect_resp \union create_resp

ClientConn == [
    send: Seq(SendRequest),
    recv: Seq(RecvRequest),
    closed: BOOLEAN \* TODO add confirmed closed
]

NullConn == (DOMAIN global_conn) \union {nil}

init_client_conn == [
    send |-> <<>>,
    recv |-> <<>>,
    closed |-> FALSE
]

ClientMainPC == {
    "Init", "ClientConnect",
    "WaitConnect", "StartSendRecv", "WaitConnClosed"
}


ClientRequest == [
    xid: Xid,
    op: {"Create"},
    group: Group,
    key: Key,
    val: Value
]

HandleQueueEntry == [
    req: ClientRequest,
    zxid: Zxid
]


---------------------------------------------------------------------------

TypeOK ==
    /\ server_log \in Seq(LogEntry)

    /\ DOMAIN server_state = Group
    /\ \A g \in Group: IsMapOf(server_state[g], SeqKey, StateInfo)

    /\ IsMapOf(active_conns, DOMAIN global_conn, ServerConnInfo)
    /\ active_sessions \subseteq Session

    /\ global_conn \in Seq(ClientConn)
    /\ client_conn \in [Client -> NullConn]
    /\ client_main_pc \in [Client -> ClientMainPC]
    /\ last_session \in [Client -> NullSession]
    /\ last_zxid \in [Client -> NullZxid]

    /\ client_send_pc \in [Client -> {"Stopped", "Start"}]
    /\ client_recv_pc \in [Client -> {"Stopped", "Start", "PushToHandle"}]

    /\ send_queue \in [Client -> Seq(ClientRequest)]
    /\ DOMAIN recv_map = Client
    /\ \A c \in Client:
        IsMapOf(recv_map[c], Xid, ClientRequest)

    /\ handle_queue \in [Client -> Seq(HandleQueueEntry)]
    /\ num_action \in 0..max_action
    /\ next_xid \in [Client -> Xid]
    /\ handled_xid \in [Client -> Xid]
    /\ local_xid \in [Client -> Xid \union {nil}]

    /\ num_conn_closed \in 0..max_conn_closed


Init ==
    /\ server_log = <<>>
    /\ server_state = [g \in Group |-> <<>>]
    /\ active_conns = <<>>
    /\ active_sessions = {}

    /\ global_conn = <<>>
    /\ client_conn = [c \in Client |-> nil]
    /\ client_main_pc = [c \in Client |-> "Init"]
    /\ last_session = [c \in Client |-> nil]
    /\ last_zxid = [c \in Client |-> nil]

    /\ client_send_pc = [c \in Client |-> "Stopped"]
    /\ client_recv_pc = [c \in Client |-> "Stopped"]
    /\ send_queue = [c \in Client |-> <<>>]
    /\ recv_map = [c \in Client |-> <<>>]
    /\ handle_queue = [c \in Client |-> <<>>]
    /\ num_action = 0
    /\ next_xid = [c \in Client |-> 30]
    /\ handled_xid = [c \in Client |-> 30]
    /\ local_xid = [c \in Client |-> nil]

    /\ num_conn_closed = 0


---------------------------------------------------------------------------

send_recv_vars == <<
    client_send_pc, client_recv_pc,
    send_queue, recv_map, handle_queue,
    num_action, next_xid, handled_xid, local_xid,
    num_conn_closed
>>

NewConnection(c) ==
    LET
        new_conn == Len(global_conn')
    IN
    /\ client_main_pc[c] = "Init"

    /\ client_main_pc' = [client_main_pc EXCEPT ![c] = "ClientConnect"]
    /\ global_conn' = Append(global_conn, init_client_conn)
    /\ client_conn' = [client_conn EXCEPT ![c] = new_conn]

    /\ UNCHANGED <<last_session, last_zxid>>
    /\ UNCHANGED send_recv_vars
    /\ UNCHANGED server_vars


conn_send(conn, req) ==
    /\ global_conn' = [global_conn EXCEPT ![conn].send = Append(@, req)]

ClientConnect(c) ==
    LET
        req == [
            type |-> "Connect",
            sess |-> nil,
            seen_zxid |-> nil
        ]

        conn == client_conn[c]
    IN
    /\ client_main_pc[c] = "ClientConnect"
    /\ client_main_pc' = [client_main_pc EXCEPT ![c] = "WaitConnect"]
    /\ conn_send(conn, req)

    /\ UNCHANGED <<client_conn, last_session, last_zxid>>
    /\ UNCHANGED send_recv_vars
    /\ UNCHANGED server_vars


ClientConnectReply(c) ==
    LET
        conn == client_conn[c]

        resp == global_conn[conn].recv[1]

        when_normal ==
            /\ ~global_conn[conn].closed
            /\ global_conn[conn].recv # <<>>
            /\ client_main_pc' = [client_main_pc EXCEPT ![c] = "StartSendRecv"]
            /\ global_conn' = [global_conn EXCEPT ![conn].recv = Tail(@)]
            /\ last_session' = [last_session EXCEPT ![c] = resp.sess]

        when_closed ==
            /\ global_conn[conn].closed
            /\ client_main_pc' = [client_main_pc EXCEPT ![c] = "Init"]
            /\ UNCHANGED global_conn
            /\ UNCHANGED last_session
    IN
    /\ client_main_pc[c] = "WaitConnect"
    /\ \/ when_normal
       \/ when_closed

    /\ UNCHANGED last_zxid
    /\ UNCHANGED client_conn
    /\ UNCHANGED send_recv_vars
    /\ UNCHANGED server_vars


ClientStartThreads(c) ==
    /\ client_main_pc[c] = "StartSendRecv"
    /\ client_main_pc' = [client_main_pc EXCEPT ![c] = "WaitConnClosed"]
    /\ client_send_pc' = [client_send_pc EXCEPT ![c] = "Start"]
    /\ client_recv_pc' = [client_recv_pc EXCEPT ![c] = "Start"]

    /\ UNCHANGED client_conn
    /\ UNCHANGED <<send_queue, recv_map, handle_queue>>
    /\ UNCHANGED <<num_action, next_xid, handled_xid>>
    /\ UNCHANGED local_xid
    /\ UNCHANGED <<last_session, last_zxid>>
    /\ UNCHANGED global_conn
    /\ UNCHANGED server_vars
    /\ UNCHANGED num_conn_closed

---------------------------------------------------------------------------

ClientCreate(c, g, k, v) ==
    LET
        req == [
            xid |-> next_xid'[c],
            op |-> "Create",
            group |-> g,
            key |-> k,
            val |-> v
        ]
    IN
    /\ num_action < max_action
    /\ num_action' = num_action + 1
    /\ next_xid' = [next_xid EXCEPT ![c] = @ + 1]
    /\ send_queue' = [send_queue EXCEPT ![c] = Append(@, req)]

    /\ UNCHANGED client_conn
    /\ UNCHANGED <<client_main_pc, client_send_pc, client_recv_pc>>
    /\ UNCHANGED <<global_conn, recv_map, handle_queue, handled_xid>>
    /\ UNCHANGED local_xid
    /\ UNCHANGED <<last_session, last_zxid>>
    /\ UNCHANGED server_vars
    /\ UNCHANGED num_conn_closed

---------------------------------------------------------------------------

send_thread_unchanged ==
    /\ UNCHANGED client_conn
    /\ UNCHANGED client_main_pc
    /\ UNCHANGED client_recv_pc
    /\ UNCHANGED <<last_session, last_zxid>>
    /\ UNCHANGED <<handle_queue>>
    /\ UNCHANGED <<next_xid, num_action, handled_xid, local_xid>>
    /\ UNCHANGED num_conn_closed

ClientHandleSend(c) ==
    LET
        conn == client_conn[c]

        req == send_queue[c][1]

        net_req == [
            type |-> "Create",
            xid |-> req.xid,
            group |-> req.group,
            key |-> req.key,
            val |-> req.val
        ]
    IN
    /\ client_send_pc[c] = "Start"

    /\ send_queue[c] # <<>>
    /\ send_queue' = [send_queue EXCEPT ![c] = Tail(@)]
    /\ recv_map' = [recv_map EXCEPT
            ![c] = mapPut(@, req.xid, req)]

    /\ global_conn' = [global_conn EXCEPT ![conn].send = Append(@, net_req)]

    /\ UNCHANGED client_send_pc
    /\ send_thread_unchanged
    /\ UNCHANGED server_vars


recv_thread_unchanged ==
    /\ UNCHANGED client_conn
    /\ UNCHANGED client_main_pc
    /\ UNCHANGED client_send_pc
    /\ UNCHANGED <<last_session>>
    /\ UNCHANGED <<send_queue>>
    /\ UNCHANGED <<next_xid, num_action, handled_xid>>
    /\ UNCHANGED num_conn_closed

ClientHandleRecv(c) ==
    LET
        conn == client_conn[c]

        resp == global_conn[conn].recv[1]

        when_normal ==
            /\ ~global_conn[conn].closed
            /\ global_conn[conn].recv # <<>>
            /\ client_recv_pc' = [client_recv_pc EXCEPT ![c] = "PushToHandle"]
            /\ global_conn' = [global_conn EXCEPT ![conn].recv = Tail(@)]
            /\ last_zxid' = [last_zxid EXCEPT ![c] = resp.zxid]
            /\ local_xid' = [local_xid EXCEPT ![c] = resp.xid]
            /\ UNCHANGED recv_map
            /\ UNCHANGED handle_queue

        when_closed ==
            /\ global_conn[conn].closed
            /\ client_recv_pc' = [client_recv_pc EXCEPT ![c] = "Stopped"]
            /\ recv_map' = [recv_map EXCEPT ![c] = <<>>]
            /\ UNCHANGED handle_queue \* TODO
            /\ UNCHANGED global_conn
            /\ UNCHANGED last_zxid
            /\ UNCHANGED local_xid
    IN
    /\ client_recv_pc[c] = "Start"
    /\ \/ when_normal
       \/ when_closed

    /\ recv_thread_unchanged
    /\ UNCHANGED server_vars


ClientRecvPushToHandle(c) ==
    LET
        xid == local_xid[c]
        req == recv_map[c][xid]

        hreq == [
            req |-> req,
            zxid |-> last_zxid[c]
        ]
    IN
    /\ client_recv_pc[c] = "PushToHandle"
    /\ client_recv_pc' = [client_recv_pc EXCEPT ![c] = "Start"]

    /\ recv_map' = [recv_map EXCEPT ![c] = mapDelete(@, xid)]
    /\ local_xid' = [local_xid EXCEPT ![c] = nil]
    /\ handle_queue' = [handle_queue EXCEPT ![c] = Append(@, hreq)]

    /\ UNCHANGED <<global_conn, last_zxid>>
    /\ recv_thread_unchanged
    /\ UNCHANGED server_vars


handle_thread_unchanged ==
    /\ UNCHANGED client_conn
    /\ UNCHANGED client_main_pc
    /\ UNCHANGED <<client_send_pc, client_recv_pc>>
    /\ UNCHANGED <<last_session>>
    /\ UNCHANGED <<send_queue, recv_map>>
    /\ UNCHANGED global_conn
    /\ UNCHANGED <<next_xid, num_action>>
    /\ UNCHANGED <<last_zxid, local_xid>>
    /\ UNCHANGED num_conn_closed

ClientDoHandle(c) ==
    LET
        hreq == handle_queue[c][1]
    IN
    /\ handle_queue[c] # <<>>
    /\ handle_queue' = [handle_queue EXCEPT ![c] = Tail(@)]
    /\ handled_xid' = [handled_xid EXCEPT ![c] = hreq.req.xid]

    /\ handle_thread_unchanged
    /\ UNCHANGED server_vars

---------------------------------------------------------------------------

ServerAcceptConn(c) ==
    LET
        conn == client_conn[c]

        new_info == [
            sess |-> nil
        ]
    IN
    /\ conn # nil
    /\ conn \notin DOMAIN active_conns
    /\ active_conns' = mapPut(active_conns, conn, new_info)

    /\ UNCHANGED global_conn
    /\ UNCHANGED active_sessions
    /\ UNCHANGED <<server_log, server_state>>

    /\ UNCHANGED client_vars
    /\ UNCHANGED aux_vars


gen_new_zxid ==
    IF server_log = <<>>
        THEN 21
        ELSE server_log[Len(server_log)].zxid + 1

doHandleConnect(conn) ==
    LET
        new_sess ==
            IF active_sessions = {}
                THEN 11
                ELSE maxOf(active_sessions) + 1

        log == [
            type |-> "NewSession",
            zxid |-> gen_new_zxid,
            sess |-> new_sess
        ]

        resp == [
            type |-> "ConnectReply",
            sess |-> new_sess
        ]
    IN
    /\ ~global_conn[conn].closed
    /\ global_conn[conn].send # <<>>
    /\ active_conns[conn].sess = nil

    /\ global_conn' = [global_conn EXCEPT
            ![conn].send = Tail(@),
            ![conn].recv = Append(@, resp)
        ]

    /\ active_sessions' = active_sessions \union {new_sess}
    /\ active_conns' = [active_conns EXCEPT ![conn].sess = new_sess]
    /\ server_log' = Append(server_log, log)

    /\ UNCHANGED server_state
    /\ UNCHANGED client_vars
    /\ UNCHANGED aux_vars

ServerHandleConnect ==
    \E conn \in DOMAIN active_conns: doHandleConnect(conn)



doHandleCreate(conn) ==
    LET
        req == global_conn[conn].send[1]

        log == [
            type |-> "Put",
            zxid |-> gen_new_zxid,
            group |-> req.group,
            key |-> req.key,
            val |-> req.val
        ]

        state_info == [
            val |-> req.val,
            sess |-> nil
        ]

        resp == [
            type |-> "CreateReply",
            xid |-> req.xid,
            zxid |-> gen_new_zxid,
            key |-> req.key
        ]
    IN
    /\ global_conn[conn].send # <<>>
    /\ global_conn' = [global_conn EXCEPT
            ![conn].send = Tail(@),
            ![conn].recv = Append(@, resp)
        ]

    /\ server_log' = Append(server_log, log)
    /\ server_state' = [server_state EXCEPT
            ![req.group] = mapPut(@, req.key, state_info)]

    /\ UNCHANGED <<active_conns, active_sessions>>
    /\ UNCHANGED client_vars
    /\ UNCHANGED aux_vars

ServerHandleCreate ==
    \E conn \in DOMAIN active_conns:
        /\ active_conns[conn].sess # nil
        /\ doHandleCreate(conn)

---------------------------------------------------------------------------

ConnectionClosed ==
    \E conn \in DOMAIN global_conn:
        /\ ~global_conn[conn].closed
        /\ num_conn_closed < max_conn_closed
        /\ num_conn_closed' = num_conn_closed + 1
        /\ global_conn' = [global_conn EXCEPT
                ![conn].closed = TRUE,
                ![conn].send = <<>>,
                ![conn].recv = <<>>
            ]
        /\ UNCHANGED server_vars
        /\ UNCHANGED client_vars

---------------------------------------------------------------------------

TerminateCond ==
    /\ \A c \in Client:
        /\ ~global_conn[client_conn[c]].closed
        /\ client_main_pc[c] = "WaitConnClosed"
        /\ client_send_pc[c] = "Start"
        /\ client_recv_pc[c] = "Start"
        /\ send_queue[c] = <<>>
        /\ handle_queue[c] = <<>>
    /\ \A conn \in DOMAIN global_conn:
        /\ global_conn[conn].send = <<>>
        /\ global_conn[conn].recv = <<>>


Terminated ==
    /\ TerminateCond
    /\ UNCHANGED vars


Next ==
    \/ \E c \in Client:
        \/ NewConnection(c)
        \/ ClientConnect(c)
        \/ ClientConnectReply(c)
        \/ ClientStartThreads(c)
        \/ ClientHandleSend(c)
        \/ ClientHandleRecv(c)
        \/ ClientRecvPushToHandle(c)
        \/ ClientDoHandle(c)
        \/ ServerAcceptConn(c)

    \/ \E c \in Client, g \in Group, k \in Key, v \in Value:
        \/ ClientCreate(c, g, k, v)

    \/ ServerHandleConnect
    \/ ServerHandleCreate

    \/ ConnectionClosed
    \/ Terminated

Spec == Init /\ [][Next]_vars

---------------------------------------------------------------------------

GlobalConnOnlyHasMaxOneOwner ==
    \A i \in DOMAIN global_conn:
        LET
            ref_set == {c \in Client: client_conn[c] = i}
        IN
            Cardinality(ref_set) <= 1



handleXidNextAction ==
    \E c \in Client:
        handled_xid' = [handled_xid EXCEPT ![c] = @ + 1]

HandledXidInv ==
    [][handleXidNextAction]_handled_xid


HandleXidOnTerminated ==
    TerminateCond =>
        (\A c \in Client: handled_xid[c] = next_xid[c])

====

------ MODULE Zookeeper ----
EXTENDS TLC, Sequences, Naturals, FiniteSets

CONSTANTS Group, Ephemeral, Key, Value,
    Client, nil, max_action

ASSUME
    /\ Ephemeral \subseteq Group
    /\ IsFiniteSet(Group)

VARIABLES server_log, server_state, active_conns, active_sessions,
    global_conn,
    client_conn, client_main_pc, last_session, last_zxid,
    client_send_pc, client_recv_pc,
    send_queue, send_notified, handle_queue, handle_notified,
    num_action, next_xid

server_vars == <<server_log, server_state, active_conns, active_sessions>>
client_vars == <<
    client_conn, client_main_pc, last_session, last_zxid,
    client_send_pc, client_recv_pc,
    send_queue, send_notified, handle_queue, handle_notified,
    num_action, next_xid
>>

vars == <<server_vars, global_conn, client_vars>>

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
            group: Group,
            key: Key
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


SendRequest == [type: {"Connect"}, sess: NullSession, seen_zxid: NullZxid]

RecvRequest == [type: {"ConnectReply"}, sess: NullSession]

ClientConn == [
    send: Seq(SendRequest),
    recv: Seq(RecvRequest),
    closed: BOOLEAN
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

Xid == 30..39

ClientRequest == [
    xid: Xid,
    op: {"Create"},
    group: Group,
    key: Key,
    val: Value
]

HandleQueueEntry == [
    req: ClientRequest
]


---------------------------------------------------------------------------

TypeOK ==
    /\ server_log \in Seq(LogEntry)
    /\ \A g \in Group: IsMapOf(server_state[g], SeqKey, StateInfo)
    /\ IsMapOf(active_conns, DOMAIN global_conn, ServerConnInfo)
    /\ active_sessions \subseteq Session

    /\ global_conn \in Seq(ClientConn)
    /\ client_conn \in [Client -> NullConn]
    /\ client_main_pc \in [Client -> ClientMainPC]
    /\ last_session \in [Client -> NullSession]
    /\ last_zxid \in [Client -> NullZxid]

    /\ client_send_pc \in [Client -> {"Stopped", "Start"}]
    /\ client_recv_pc \in [Client -> {"Stopped", "Start"}]
    /\ send_queue \in [Client -> Seq(ClientRequest)]
    /\ send_notified \in BOOLEAN
    /\ handle_queue \in [Client -> Seq(HandleQueueEntry)]
    /\ handle_notified \in BOOLEAN
    /\ num_action \in 0..max_action
    /\ next_xid \in Xid


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
    /\ handle_queue = [c \in Client |-> <<>>]
    /\ num_action = 0
    /\ next_xid = 30


---------------------------------------------------------------------------

send_recv_vars == <<
    client_send_pc, client_recv_pc,
    send_queue, handle_queue, num_action, next_xid
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
    IN
    /\ client_main_pc[c] = "WaitConnect"
    /\ Len(global_conn[conn].recv) > 0

    /\ client_main_pc' = [client_main_pc EXCEPT ![c] = "StartSendRecv"]
    /\ global_conn' = [global_conn EXCEPT ![conn].recv = Tail(@)]
    /\ last_session' = [last_session EXCEPT ![c] = resp.sess]

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
    /\ UNCHANGED <<send_queue, handle_queue, num_action, next_xid>>
    /\ UNCHANGED <<last_session, last_zxid>>
    /\ UNCHANGED global_conn
    /\ UNCHANGED server_vars

---------------------------------------------------------------------------

ClientCreate(c, g, k, v) ==
    LET
        req == [
            xid |-> next_xid',
            op |-> "Create",
            group |-> g,
            key |-> k,
            val |-> v
        ]
    IN
    /\ num_action < max_action
    /\ num_action' = num_action + 1
    /\ next_xid' = next_xid + 1
    /\ send_queue' = [send_queue EXCEPT ![c] = Append(@, req)]

    /\ UNCHANGED client_conn
    /\ UNCHANGED <<client_main_pc, client_send_pc, client_recv_pc>>
    /\ UNCHANGED <<global_conn, handle_queue>>
    /\ UNCHANGED <<last_session, last_zxid>>
    /\ UNCHANGED server_vars

---------------------------------------------------------------------------

ClientHandleSend(c) ==
    /\ send_queue[c] # <<>>
    /\ client_send_pc[c] = "Start"

    /\ UNCHANGED <<last_session, last_zxid>>
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


doHandleConnect(conn) ==
    LET
        new_sess ==
            IF active_sessions = {}
                THEN 11
                ELSE maxOf(active_sessions) + 1

        new_zxid ==
            IF server_log = <<>>
                THEN 21
                ELSE server_log[Len(server_log)].zxid + 1

        log == [
            type |-> "NewSession",
            zxid |-> new_zxid,
            sess |-> new_sess
        ]

        resp == [
            type |-> "ConnectReply",
            sess |-> new_sess
        ]
    IN
    /\ Len(global_conn[conn].send) > 0
    /\ global_conn' = [global_conn EXCEPT
            ![conn].send = Tail(@),
            ![conn].recv = Append(@, resp)
        ]

    /\ active_sessions' = active_sessions \union {new_sess}
    /\ server_log' = Append(server_log, log)

    /\ UNCHANGED server_state
    /\ UNCHANGED active_conns
    /\ UNCHANGED client_vars

ServerHandleConnect ==
    \E conn \in DOMAIN active_conns: doHandleConnect(conn)

---------------------------------------------------------------------------

TerminateCond ==
    /\ \A c \in Client:
        /\ client_main_pc[c] = "WaitConnClosed"
        /\ client_send_pc[c] = "Start"
        /\ client_recv_pc[c] = "Start"
        /\ send_queue[c] = <<>>
        /\ handle_queue[c] = <<>>


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
        \/ ServerAcceptConn(c)

    \/ \E c \in Client, g \in Group, k \in Key, v \in Value:
        \/ ClientCreate(c, g, k, v)

    \/ ServerHandleConnect
    \/ Terminated

Spec == Init /\ [][Next]_vars

---------------------------------------------------------------------------

GlobalConnOnlyHasMaxOneOwner ==
    \A i \in DOMAIN global_conn:
        LET
            ref_set == {c \in Client: client_conn[c] = i}
        IN
            Cardinality(ref_set) <= 1

====

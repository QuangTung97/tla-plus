------ MODULE Zookeeper ----
EXTENDS TLC, Sequences, Naturals, FiniteSets

CONSTANTS Group, Ephemeral, Key, Value, Client, nil

ASSUME
    /\ Ephemeral \subseteq Group
    /\ IsFiniteSet(Group)

VARIABLES server_log, server_state, active_conns, active_sessions,
    global_conn,
    client_conn, client_main_pc, last_session, last_zxid

server_vars == <<server_log, server_state, active_conns, active_sessions>>
client_vars == <<client_conn, client_main_pc, last_session, last_zxid>>

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

---------------------------------------------------------------------------

Zxid == 21..29

NullZxid == Zxid \union {nil}


Session == 11..19

NullSession == Session \union {nil}


LogEntry == [type: {"Put"}, group: Group, key: Key]


SeqKey == Key \union (Key \X (1..20))

StateInfo == [
    val: Value,
    sess: NullSession \* For Ephemeral ZNodes
]

ServerConnInfo == [
    sess: NullSession
]


SendRequest == [type: {"Connect"}, sess: NullSession, seen_zxid: NullZxid]

RecvRequest == [type: {"ConnectReply"}]

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

ClientMainPC == {"Init", "ClientConnect", "WaitConnect"}

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


---------------------------------------------------------------------------

NewConnection(c) ==
    LET
        new_conn == Len(global_conn')
    IN
    /\ client_main_pc[c] = "Init"

    /\ client_main_pc' = [client_main_pc EXCEPT ![c] = "ClientConnect"]
    /\ global_conn' = Append(global_conn, init_client_conn)
    /\ client_conn' = [client_conn EXCEPT ![c] = new_conn]

    /\ UNCHANGED <<last_session, last_zxid>>
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
    /\ UNCHANGED server_vars


ClientConnectReply(c) ==
    LET
        conn == client_conn[c]
    IN
    /\ client_main_pc[c] = "WaitConnect"
    /\ Len(global_conn[conn].recv) > 0

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

---------------------------------------------------------------------------

TerminateCond ==
    /\ \A c \in Client: client_main_pc[c] = "WaitClosed"

Terminated ==
    /\ TerminateCond
    /\ UNCHANGED vars


Next ==
    \/ \E c \in Client:
        \/ NewConnection(c)
        \/ ClientConnect(c)
        \/ ClientConnectReply(c)
        \/ ServerAcceptConn(c)
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

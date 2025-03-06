------ MODULE Zookeeper ----
EXTENDS TLC, Sequences, Naturals, FiniteSets, Common

CONSTANTS Group, Ephemeral, Key, Value,
    Client, nil, max_action, max_fail

ASSUME
    /\ Ephemeral \subseteq Group
    /\ IsFiniteSet(Group)

VARIABLES
    server_log, server_state, active_conns,
    active_sessions, server_children, \* children watch
    global_conn,
    client_conn, client_main_pc, last_session, last_zxid,
    client_send_pc, client_recv_pc, client_status,
    client_children, \* children watch
    send_queue, recv_map, handle_queue,
    num_action, next_xid, handled_xid, local_resp,
    num_fail,
    core_num_fail, expect_send, expect_recv,
    test_zk_client_req, test_zk_recv_req, test_zk_children

server_vars == <<
    server_log, server_state, active_conns,
    active_sessions, server_children
>>
client_vars == <<
    client_conn, client_main_pc, last_session, last_zxid,
    client_send_pc, client_recv_pc, client_status,
    client_children,
    send_queue, recv_map, handle_queue,
    num_action, next_xid, handled_xid, local_resp
>>

aux_vars == <<num_fail, core_num_fail, expect_send, expect_recv>>
match_vars == <<test_zk_client_req, test_zk_recv_req, test_zk_children>>
vars == <<server_vars, global_conn, client_vars, aux_vars, match_vars>>

---------------------------------------------------------------------------

new_handle_req(req, zxid, status) == [
    req |-> req,
    zxid |-> zxid,
    resp |-> nil,
    status |-> status
]

failed_hreq_from_recv_map(c) ==
    LET
        xid_set == DOMAIN recv_map[c]

        recv_map_xid ==
            IF xid_set = {}
                THEN <<>>
                ELSE seqRange(minOf(xid_set), maxOf(xid_set))

        num_key == Len(recv_map_xid)

        failed_hreq(i) == new_handle_req(
            recv_map[c][recv_map_xid[i]], nil, "NetErr"
        )
    IN
    [i \in 1..num_key |-> failed_hreq(i)]

zk_client_req ==
    LET
        conn(c) == global_conn[client_conn[c]]

        conn_sending(c) ==
            IF client_conn[c] = nil THEN
                <<>>
            ELSE
                expect_send[c] \o conn(c).send
    IN
    [c \in Client |-> conn_sending(c) \o send_queue[c]]

zk_recv_req ==
    LET
        conn(c) == global_conn[client_conn[c]]

        mapped(c) ==
            IF client_conn[c] = nil THEN
                <<>>
            ELSE
                expect_recv[c] \o conn(c).recv
    IN
    [c \in Client |-> mapped(c)]

zk_server_children_watch ==
    LET
        client_of_sess_set(sess) == {c \in Client: last_session[c] = sess}

        client_of_sess(sess) ==
            IF client_of_sess_set(sess) = {}
                THEN nil
                ELSE CHOOSE c \in client_of_sess_set(sess): TRUE

        conn_of_sess(sess) ==
            IF client_of_sess(sess) = nil
                THEN nil
                ELSE client_conn[client_of_sess(sess)]

        children_watch_of(sess) ==
            mapGet(server_children, conn_of_sess(sess), {})

        sess_with_non_null_watch ==
            {sess \in active_sessions: children_watch_of(sess) # {}}
    IN
        [sess \in sess_with_non_null_watch |-> children_watch_of(sess)]


ZK == INSTANCE Core WITH
    client_req <- zk_client_req,
    recv_req <- zk_recv_req,
    handle_req <- handle_queue,
    client_sess <- last_session,
    active_sess <- active_sessions,
    server_children_watch <- zk_server_children_watch,
    num_fail <- core_num_fail,
    value_range <- 10

---------------------------------------------------------------------------

Zxid == ZK!Zxid
NullZxid == ZK!NullZxid
Session == ZK!Session
NullSession == ZK!NullSession
Xid == ZK!Xid

LogEntry == ZK!LogEntry

StateInfo == ZK!StateInfo

ServerConnInfo == [
    sess: NullSession
]


ClientRequest == ZK!ClientRequest

HandleRequest == ZK!HandleRequest

ClientConn == [
    send: Seq(ClientRequest),
    recv: Seq(HandleRequest),
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

---------------------------------------------------------------------------

CoreTypeOK == ZK!TypeOK

CheckTypeOK ==
    /\ handle_queue \in [Client -> Seq(ZK!HandleRequest)]

TypeOK ==
    /\ server_log \in Seq(LogEntry)

    /\ DOMAIN server_state = Group
    /\ \A g \in Group: IsMapOf(server_state[g], Key, StateInfo)

    /\ IsMapOf(active_conns, DOMAIN global_conn, ServerConnInfo)
    /\ active_sessions \subseteq Session
    /\ IsMapOf(server_children, DOMAIN global_conn, SUBSET Group)

    /\ global_conn \in Seq(ClientConn)
    /\ client_conn \in [Client -> NullConn]
    /\ client_main_pc \in [Client -> ClientMainPC]
    /\ last_session \in [Client -> NullSession]
    /\ last_zxid \in [Client -> NullZxid]

    /\ client_send_pc \in [Client -> {"Stopped", "Start", "Sleep"}]
    /\ client_recv_pc \in [Client -> {"Stopped", "Start", "PushToHandle"}]
    /\ client_status \in [Client -> {"Connecting", "HasSession", "Disconnected"}]
    /\ client_children \in [Client -> SUBSET Group]

    /\ send_queue \in [Client -> Seq(ClientRequest)]
    /\ DOMAIN recv_map = Client
    /\ \A c \in Client:
        IsMapOf(recv_map[c], Xid, ClientRequest)

    /\ handle_queue \in [Client -> Seq(HandleRequest)]
    /\ num_action \in 0..max_action
    /\ next_xid \in [Client -> Xid]
    /\ handled_xid \in [Client -> Xid]
    /\ local_resp \in [Client -> HandleRequest \union {nil}]

    /\ num_fail \in 0..max_fail
    /\ core_num_fail \in 0..max_fail
    /\ core_num_fail <= num_fail
    /\ expect_send \in [Client -> Seq(ClientRequest)]
    /\ expect_recv \in [Client -> Seq(HandleRequest)]

    /\ test_zk_client_req \in [Client -> Seq(ClientRequest)]
    /\ test_zk_recv_req \in [Client -> Seq(HandleRequest)]
    /\ IsMapOf(test_zk_children, active_sessions, SUBSET Group)


Init ==
    /\ server_log = <<>>
    /\ server_state = [g \in Group |-> <<>>]
    /\ active_conns = <<>>
    /\ active_sessions = {}
    /\ server_children = <<>>

    /\ global_conn = <<>>
    /\ client_conn = [c \in Client |-> nil]
    /\ client_main_pc = [c \in Client |-> "Init"]
    /\ last_session = [c \in Client |-> nil]
    /\ last_zxid = [c \in Client |-> nil]

    /\ client_send_pc = [c \in Client |-> "Stopped"]
    /\ client_recv_pc = [c \in Client |-> "Stopped"]
    /\ client_status = [c \in Client |-> "Disconnected"]
    /\ client_children = [c \in Client |-> {}]

    /\ send_queue = [c \in Client |-> <<>>]
    /\ recv_map = [c \in Client |-> <<>>]
    /\ handle_queue = [c \in Client |-> <<>>]
    /\ num_action = 0
    /\ next_xid = [c \in Client |-> 30]
    /\ handled_xid = [c \in Client |-> 30]
    /\ local_resp = [c \in Client |-> nil]

    /\ num_fail = 0
    /\ core_num_fail = 0
    /\ expect_send = [c \in Client |-> <<>>]
    /\ expect_recv = [c \in Client |-> <<>>]

    /\ test_zk_client_req = zk_client_req
    /\ test_zk_recv_req = zk_recv_req
    /\ test_zk_children = zk_server_children_watch


---------------------------------------------------------------------------

auto_update ==
    \* /\ test_zk_client_req' = zk_client_req'
    \* /\ test_zk_recv_req' = zk_recv_req'
    /\ test_zk_children' = zk_server_children_watch'
    /\ UNCHANGED test_zk_client_req
    /\ UNCHANGED test_zk_recv_req

send_recv_vars == <<
    client_send_pc, client_recv_pc,
    send_queue, recv_map,
    num_action, next_xid, handled_xid, local_resp,
    num_fail
>>

NewConnection(c) ==
    LET
        new_conn == Len(global_conn')
    IN
    /\ client_main_pc[c] = "Init"

    /\ client_main_pc' = [client_main_pc EXCEPT ![c] = "ClientConnect"]
    /\ global_conn' = Append(global_conn, init_client_conn)
    /\ client_conn' = [client_conn EXCEPT ![c] = new_conn]

    /\ UNCHANGED client_status
    /\ UNCHANGED client_children
    /\ UNCHANGED <<last_session, last_zxid>>
    /\ UNCHANGED send_recv_vars
    /\ UNCHANGED <<core_num_fail, expect_send, expect_recv>>
    /\ UNCHANGED handle_queue
    /\ UNCHANGED server_vars
    /\ auto_update


conn_send(conn, req) ==
    /\ global_conn' = [global_conn EXCEPT ![conn].send = Append(@, req)]

ClientConnect(c) ==
    LET
        req == [
            type |-> "Connect",
            sess |-> last_session[c],
            seen_zxid |-> nil \* TODO
        ]

        conn == client_conn[c]

        when_normal ==
            /\ ~global_conn[conn].closed
            /\ client_main_pc' = [client_main_pc EXCEPT ![c] = "WaitConnect"]
            /\ conn_send(conn, req)
            /\ client_status' = [client_status EXCEPT ![c] = "Connecting"]

        when_closed ==
            /\ global_conn[conn].closed
            /\ client_main_pc' = [client_main_pc EXCEPT ![c] = "Init"]
            /\ client_status' = [client_status EXCEPT ![c] = "Disconnected"]
            /\ UNCHANGED global_conn
    IN
    /\ client_main_pc[c] = "ClientConnect"
    /\ \/ when_normal
       \/ when_closed

    /\ UNCHANGED client_children
    /\ UNCHANGED <<client_conn, last_session, last_zxid>>
    /\ UNCHANGED handle_queue
    /\ UNCHANGED send_recv_vars
    /\ UNCHANGED server_vars
    /\ UNCHANGED <<core_num_fail, expect_send, expect_recv>>
    /\ auto_update


ClientConnectReply(c) ==
    LET
        conn == client_conn[c]

        resp == global_conn[conn].recv[1]

        when_normal ==
            /\ ~global_conn[conn].closed
            /\ global_conn[conn].recv # <<>>
            /\ resp.sess # nil
            /\ client_main_pc' = [client_main_pc EXCEPT ![c] = "StartSendRecv"]
            /\ global_conn' = [global_conn EXCEPT ![conn].recv = Tail(@)]
            /\ last_session' = [last_session EXCEPT ![c] = resp.sess]
            /\ client_status' = [client_status EXCEPT ![c] = "HasSession"]
            /\ handle_queue' = [handle_queue EXCEPT ![c] = Append(@, resp)]
            /\ UNCHANGED client_children \* TODO
            /\ UNCHANGED core_num_fail

        when_sess_expired ==
            /\ ~global_conn[conn].closed
            /\ global_conn[conn].recv # <<>>
            /\ resp.sess = nil
            /\ client_main_pc' = [client_main_pc EXCEPT ![c] = "Init"]
            /\ global_conn' = [global_conn EXCEPT
                    ![conn].recv = Tail(@),
                    ![conn].closed = TRUE
                ]
            /\ last_session' = [last_session EXCEPT ![c] = nil]
            /\ client_status' = [client_status EXCEPT ![c] = "Disconnected"]
            /\ UNCHANGED client_children
            /\ UNCHANGED handle_queue
            /\ UNCHANGED core_num_fail

        when_closed ==
            /\ global_conn[conn].closed
            /\ client_main_pc' = [client_main_pc EXCEPT ![c] = "Init"]
            /\ client_status' = [client_status EXCEPT ![c] = "Disconnected"]
            /\ core_num_fail' = core_num_fail + 1
            /\ UNCHANGED client_children
            /\ UNCHANGED handle_queue
            /\ UNCHANGED global_conn
            /\ UNCHANGED last_session
    IN
    /\ client_main_pc[c] = "WaitConnect"
    /\ \/ when_normal
       \/ when_sess_expired
       \/ when_closed

    /\ expect_recv' = [expect_recv EXCEPT ![c] = <<>>]
    /\ expect_send' = [expect_send EXCEPT ![c] = <<>>]

    /\ UNCHANGED last_zxid
    /\ UNCHANGED client_conn
    /\ UNCHANGED send_recv_vars
    /\ UNCHANGED server_vars
    /\ auto_update


ClientStartThreads(c) ==
    /\ client_main_pc[c] = "StartSendRecv"
    /\ client_main_pc' = [client_main_pc EXCEPT ![c] = "WaitConnClosed"]
    /\ client_send_pc' = [client_send_pc EXCEPT ![c] = "Start"]
    /\ client_recv_pc' = [client_recv_pc EXCEPT ![c] = "Start"]

    /\ UNCHANGED client_conn
    /\ UNCHANGED client_status
    /\ UNCHANGED client_children
    /\ UNCHANGED <<send_queue, recv_map, handle_queue>>
    /\ UNCHANGED <<num_action, next_xid, handled_xid>>
    /\ UNCHANGED local_resp
    /\ UNCHANGED <<last_session, last_zxid>>
    /\ UNCHANGED global_conn
    /\ UNCHANGED server_vars
    /\ UNCHANGED aux_vars
    /\ auto_update

---------------------------------------------------------------------------

notify_send_thread(c) ==
    IF client_send_pc[c] = "Sleep"
        THEN client_send_pc' = [client_send_pc EXCEPT ![c] = "Start"]
        ELSE UNCHANGED client_send_pc


action_unchanged ==
    /\ UNCHANGED client_conn
    /\ UNCHANGED <<client_main_pc, client_recv_pc>>
    /\ UNCHANGED client_status
    /\ UNCHANGED <<global_conn, recv_map, handled_xid>>
    /\ UNCHANGED local_resp
    /\ UNCHANGED <<last_session, last_zxid>>
    /\ UNCHANGED server_vars
    /\ UNCHANGED aux_vars
    /\ UNCHANGED client_children
    /\ auto_update


push_to_send_queue(c, req) ==
    LET
        when_has_sess ==
            /\ send_queue' = [send_queue EXCEPT ![c] = Append(@, req)]
            /\ notify_send_thread(c)
            /\ UNCHANGED handle_queue

        hreq == new_handle_req(req, nil, "NetErr")

        when_not_has_sess ==
            /\ handle_queue' = [handle_queue EXCEPT ![c] = Append(@, hreq)]
            /\ UNCHANGED send_queue
            /\ UNCHANGED client_send_pc
    IN
    IF client_status[c] = "HasSession"
        THEN when_has_sess
        ELSE when_not_has_sess


ClientCreate(c, g, k, v) ==
    LET
        req == [
            xid |-> next_xid'[c],
            type |-> "Create",
            group |-> g,
            key |-> k,
            val |-> v
        ]
    IN
    /\ num_action < max_action
    /\ num_action' = num_action + 1
    /\ next_xid' = [next_xid EXCEPT ![c] = @ + 1]
    /\ push_to_send_queue(c, req)

    /\ action_unchanged


ClientChildren(c, g) ==
    LET
        req == [
            xid |-> next_xid'[c],
            type |-> "Children",
            group |-> g
        ]
    IN
    /\ num_action < max_action
    /\ num_action' = num_action + 1
    /\ next_xid' = [next_xid EXCEPT ![c] = @ + 1]
    /\ push_to_send_queue(c, req)

    /\ action_unchanged

---------------------------------------------------------------------------

send_thread_unchanged ==
    /\ UNCHANGED client_conn
    /\ UNCHANGED client_main_pc
    /\ UNCHANGED client_status
    /\ UNCHANGED client_children
    /\ UNCHANGED client_recv_pc
    /\ UNCHANGED <<last_session, last_zxid>>
    /\ UNCHANGED <<handle_queue>>
    /\ UNCHANGED <<next_xid, num_action, handled_xid, local_resp>>
    /\ UNCHANGED <<num_fail, core_num_fail, expect_recv>>
    /\ auto_update


ClientHandleSend(c) ==
    LET
        conn == client_conn[c]
        req == send_queue[c][1]
        is_closed == global_conn[conn].closed

        send_to_conn ==
            /\ global_conn' = [global_conn EXCEPT
                    ![conn].send = Append(@, req)]

        when_normal ==
            /\ send_queue' = [send_queue EXCEPT ![c] = Tail(@)]
            /\ recv_map' = [recv_map EXCEPT
                    ![c] = mapPut(@, req.xid, req)]
            /\ IF is_closed
                THEN
                    /\ UNCHANGED global_conn
                    /\ expect_send' = [expect_send EXCEPT ![c] = Append(@, req)]
                ELSE
                    /\ send_to_conn
                    /\ UNCHANGED expect_send
            /\ UNCHANGED client_send_pc

        when_disconnected ==
            /\ client_send_pc' = [client_send_pc EXCEPT ![c] = "Stopped"]
            /\ UNCHANGED expect_send
            /\ UNCHANGED recv_map
            /\ UNCHANGED global_conn
            /\ UNCHANGED send_queue
            /\ UNCHANGED client_status

        goto_sleep ==
            /\ client_send_pc' = [client_send_pc EXCEPT ![c] = "Sleep"]
            /\ UNCHANGED recv_map
            /\ UNCHANGED global_conn
            /\ UNCHANGED send_queue
            /\ UNCHANGED client_status
            /\ UNCHANGED expect_send

        do_handle_send ==
            IF client_status[c] # "HasSession" THEN
                when_disconnected
            ELSE IF send_queue[c] # <<>> THEN
                when_normal
            ELSE
                goto_sleep
    IN
    /\ client_send_pc[c] = "Start"
    /\ do_handle_send

    /\ UNCHANGED server_vars
    /\ send_thread_unchanged


recv_thread_unchanged ==
    /\ UNCHANGED client_conn
    /\ UNCHANGED client_main_pc
    /\ UNCHANGED <<last_session>>
    /\ UNCHANGED <<next_xid, num_action, handled_xid>>
    /\ UNCHANGED <<num_fail>>
    /\ auto_update


ClientHandleRecv(c) ==
    LET
        conn == client_conn[c]

        resp == global_conn[conn].recv[1]

        when_normal ==
            /\ client_recv_pc' = [client_recv_pc EXCEPT ![c] = "PushToHandle"]
            /\ global_conn' = [global_conn EXCEPT ![conn].recv = Tail(@)]
            /\ last_zxid' = [last_zxid EXCEPT ![c] = resp.zxid]
            /\ local_resp' = [local_resp EXCEPT ![c] = resp]
            /\ expect_recv' = [expect_recv EXCEPT ![c] = Append(@, resp)]
            /\ UNCHANGED client_children
            /\ UNCHANGED expect_send
            /\ UNCHANGED core_num_fail
            /\ UNCHANGED recv_map
            /\ UNCHANGED handle_queue
            /\ UNCHANGED client_status
            /\ UNCHANGED send_queue
            /\ UNCHANGED client_send_pc

        pushed == failed_hreq_from_recv_map(c)

        remain_hreq(i) == new_handle_req(send_queue[c][i], nil, "NetErr")

        send_queue_remain == [i \in DOMAIN send_queue[c] |-> remain_hreq(i)]

        when_closed ==
            /\ client_recv_pc' = [client_recv_pc EXCEPT ![c] = "Stopped"]
            /\ recv_map' = [recv_map EXCEPT ![c] = <<>>]
            /\ client_status' = [client_status EXCEPT ![c] = "Disconnected"]
            /\ handle_queue' = [handle_queue
                    EXCEPT ![c] = @ \o pushed \o send_queue_remain]
            /\ send_queue' = [send_queue EXCEPT ![c] = <<>>]
            /\ notify_send_thread(c)

            /\ core_num_fail' = core_num_fail + 1
            /\ expect_send' = [expect_send EXCEPT ![c] = <<>>]
            /\ expect_recv' = [expect_recv EXCEPT ![c] = <<>>]

            /\ UNCHANGED client_children
            /\ UNCHANGED global_conn
            /\ UNCHANGED last_zxid
            /\ UNCHANGED local_resp

        do_handle_recv ==
            IF global_conn[conn].closed THEN
                when_closed
            ELSE IF global_conn[conn].recv # <<>> THEN
                when_normal
            ELSE
                FALSE
    IN
    /\ client_recv_pc[c] = "Start"
    /\ do_handle_recv

    /\ UNCHANGED server_vars
    /\ recv_thread_unchanged


ClientRecvPushToHandle(c) ==
    LET
        hreq == local_resp[c]
        xid == hreq.req.xid
    IN
    /\ client_recv_pc[c] = "PushToHandle"
    /\ client_recv_pc' = [client_recv_pc EXCEPT ![c] = "Start"]

    /\ recv_map' = [recv_map EXCEPT ![c] = mapDelete(@, xid)]
    /\ local_resp' = [local_resp EXCEPT ![c] = nil]
    /\ handle_queue' = [handle_queue EXCEPT ![c] = Append(@, hreq)]
    /\ expect_recv' = [expect_recv EXCEPT ![c] = Tail(@)]

    /\ UNCHANGED client_children \* TODO
    /\ UNCHANGED <<expect_send, core_num_fail>>
    /\ UNCHANGED client_status
    /\ UNCHANGED send_queue
    /\ UNCHANGED client_send_pc
    /\ UNCHANGED <<global_conn, last_zxid>>
    /\ UNCHANGED server_vars
    /\ recv_thread_unchanged


handle_thread_unchanged ==
    /\ UNCHANGED client_conn
    /\ UNCHANGED client_main_pc
    /\ UNCHANGED client_status
    /\ UNCHANGED <<client_send_pc, client_recv_pc>>
    /\ UNCHANGED <<last_session>>
    /\ UNCHANGED <<send_queue, recv_map>>
    /\ UNCHANGED global_conn
    /\ UNCHANGED <<next_xid, num_action>>
    /\ UNCHANGED <<last_zxid, local_resp>>
    /\ UNCHANGED aux_vars
    /\ UNCHANGED client_children
    /\ auto_update

ClientDoHandle(c) ==
    LET
        hreq == handle_queue[c][1]
    IN
    /\ handle_queue[c] # <<>>
    /\ handle_queue' = [handle_queue EXCEPT ![c] = Tail(@)]
    /\ IF "req" \in DOMAIN hreq
        THEN handled_xid' = [handled_xid EXCEPT ![c] = hreq.req.xid]
        ELSE UNCHANGED handled_xid

    /\ UNCHANGED server_vars
    /\ handle_thread_unchanged


ClientWaitConnClosed(c) ==
    /\ client_main_pc[c] = "WaitConnClosed"
    /\ client_send_pc[c] = "Stopped"
    /\ client_recv_pc[c] = "Stopped"

    /\ client_main_pc' = [client_main_pc EXCEPT ![c] = "Init"]
    /\ client_conn' = [client_conn EXCEPT ![c] = nil]

    /\ UNCHANGED client_status
    /\ UNCHANGED client_children
    /\ UNCHANGED <<client_send_pc, client_recv_pc>>
    /\ UNCHANGED global_conn
    /\ UNCHANGED <<send_queue, handle_queue, recv_map>>
    /\ UNCHANGED <<next_xid, handled_xid, local_resp>>
    /\ UNCHANGED <<last_session, last_zxid>>
    /\ UNCHANGED num_action

    /\ UNCHANGED server_vars
    /\ UNCHANGED aux_vars
    /\ auto_update

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
    /\ UNCHANGED <<server_log, server_state, server_children>>

    /\ UNCHANGED client_vars
    /\ UNCHANGED aux_vars
    /\ auto_update


gen_new_zxid ==
    IF server_log = <<>>
        THEN 21
        ELSE server_log[Len(server_log)].zxid + 1

current_client(conn) ==
    LET
        client_with_conn == {c \in Client: client_conn[c] = conn}
    IN
    IF client_with_conn = {}
        THEN nil
        ELSE (CHOOSE c \in client_with_conn: TRUE)


doHandleConnect(conn) ==
    LET
        new_sess == ZK!new_sess

        log == [
            type |-> "NewSession",
            zxid |-> gen_new_zxid,
            sess |-> new_sess
        ]

        new_resp(sess_val) == [
            type |-> "ConnectReply",
            sess |-> sess_val
        ]

        req == global_conn[conn].send[1]

        when_req_no_sess ==
            /\ global_conn' = [global_conn EXCEPT
                    ![conn].send = Tail(@),
                    ![conn].recv = Append(@, new_resp(new_sess))
                ]
            /\ active_sessions' = active_sessions \union {new_sess}
            /\ active_conns' = [active_conns EXCEPT ![conn].sess = new_sess]
            /\ server_log' = Append(server_log, log)

        when_req_has_sess_active ==
            /\ global_conn' = [global_conn EXCEPT
                    ![conn].send = Tail(@),
                    ![conn].recv = Append(@, new_resp(req.sess))
                ]
            /\ active_conns' = [active_conns EXCEPT ![conn].sess = req.sess]
            /\ UNCHANGED active_sessions
            /\ UNCHANGED server_log

        when_req_has_sess_deleted ==
            /\ global_conn' = [global_conn EXCEPT
                    ![conn].send = Tail(@),
                    ![conn].recv = Append(@, new_resp(nil))
                ]
            /\ UNCHANGED active_conns
            /\ UNCHANGED active_sessions
            /\ UNCHANGED server_log
    IN
    /\ ~global_conn[conn].closed
    /\ global_conn[conn].send # <<>>
    /\ active_conns[conn].sess = nil

    /\ IF req.sess = nil THEN
            when_req_no_sess
        ELSE IF req.sess \in active_sessions THEN
            when_req_has_sess_active
        ELSE
            when_req_has_sess_deleted

    /\ UNCHANGED server_state
    /\ UNCHANGED server_children
    /\ UNCHANGED client_vars
    /\ UNCHANGED <<num_fail, core_num_fail, expect_send, expect_recv>>
    /\ auto_update

ServerHandleConnect ==
    \E conn \in DOMAIN active_conns: doHandleConnect(conn)


server_consume_and_resp(conn, resp) ==
    /\ global_conn[conn].send # <<>>
    /\ global_conn' = [global_conn EXCEPT
            ![conn].send = Tail(@),
            ![conn].recv = Append(@, resp)
        ]

server_consume_and_resp_multi(conn, resp_list) ==
    /\ global_conn[conn].send # <<>>
    /\ global_conn' = [global_conn EXCEPT
            ![conn].send = Tail(@),
            ![conn].recv = @ \o resp_list
        ]


doHandleCreate(conn) ==
    LET
        req == global_conn[conn].send[1]
        g == req.group
        k == req.key

        log == [
            type |-> "Put",
            zxid |-> gen_new_zxid,
            group |-> g,
            key |-> k,
            val |-> req.val
        ]

        state_info == [
            val |-> req.val,
            sess |-> nil
        ]

        hreq == new_handle_req(req, gen_new_zxid, "OK")
        failed_hreq == new_handle_req(req, nil, "Existed")

        is_existed ==
            /\ k \in DOMAIN server_state[g]

        when_existed ==
            /\ server_consume_and_resp(conn, failed_hreq)
            /\ UNCHANGED server_log
            /\ UNCHANGED server_state
            /\ UNCHANGED server_children

        old_watch == mapGet(server_children, conn, {})

        push_to_conn_with_watch ==
            IF g \in old_watch THEN
                /\ server_consume_and_resp_multi(conn, <<hreq>>)
                /\ server_children' = mapDelete(server_children, conn)
            ELSE
                /\ server_consume_and_resp(conn, hreq)
                /\ UNCHANGED server_children

        when_not_existed ==
            /\ push_to_conn_with_watch
            /\ server_log' = Append(server_log, log)
            /\ server_state' = [server_state EXCEPT
                    ![g] = mapPut(@, k, state_info)]
    IN
    /\ global_conn[conn].send # <<>>
    /\ req.type = "Create"
    /\ IF is_existed
        THEN when_existed
        ELSE when_not_existed

    /\ UNCHANGED <<active_conns, active_sessions>>
    /\ UNCHANGED client_vars
    /\ UNCHANGED aux_vars

doHandleChildren(conn) ==
    LET
        req == global_conn[conn].send[1]
        g == req.group

        log == [
            type |-> "Put",
            zxid |-> gen_new_zxid,
            group |-> req.group,
            key |-> req.key,
            val |-> req.val
        ]

        children == [
            children |-> DOMAIN server_state[g]
        ]

        hreq == ZK!new_handle_with_resp(req, gen_new_zxid, children, "OK")

        old_watch == mapGet(server_children, conn, {})
        new_watch == old_watch \union {g}
    IN
    /\ server_consume_and_resp(conn, hreq)
    /\ req.type = "Children"

    /\ server_children' = mapPut(server_children, conn, new_watch)

    /\ UNCHANGED server_log
    /\ UNCHANGED server_state

    /\ UNCHANGED <<active_conns, active_sessions>>
    /\ UNCHANGED client_vars
    /\ UNCHANGED aux_vars

ServerHandleRequest ==
    \E conn \in DOMAIN active_conns:
        /\ active_conns[conn].sess # nil
        /\ \/ doHandleCreate(conn)
           \/ doHandleChildren(conn)
        /\ auto_update


ServerRemoveActiveConn ==
    \E conn \in DOMAIN active_conns:
        /\ active_conns[conn].sess # nil
        /\ global_conn[conn].closed
        /\ active_conns' = mapDelete(active_conns, conn)

        /\ UNCHANGED global_conn
        /\ UNCHANGED server_children \* TODO check invariant
        /\ UNCHANGED <<server_log, server_state>>
        /\ UNCHANGED active_sessions
        /\ UNCHANGED client_vars
        /\ UNCHANGED aux_vars
        /\ auto_update


ServerLoseSession ==
    \E sess \in active_sessions:
        LET
            has_active_conn ==
                \E conn \in DOMAIN global_conn:
                    conn \in DOMAIN active_conns

            no_active_conn == ~has_active_conn

            log_entry == [
                type |-> "DeleteSession",
                zxid |-> gen_new_zxid,
                sess |-> sess
            ]
        IN
        /\ no_active_conn
        /\ num_fail < max_fail
        /\ num_fail' = num_fail + 1
        /\ core_num_fail' = core_num_fail + 1

        /\ active_sessions' = active_sessions \ {sess}
        /\ server_log' = Append(server_log, log_entry)
        /\ UNCHANGED server_state
        /\ UNCHANGED server_children

        /\ UNCHANGED active_conns
        /\ UNCHANGED global_conn
        /\ UNCHANGED client_vars
        /\ UNCHANGED <<expect_send, expect_recv>>
        /\ auto_update



---------------------------------------------------------------------------

ConnectionClosed ==
    \E conn \in DOMAIN global_conn:
        LET
            curr == current_client(conn)
            conn_val == global_conn[conn]
        IN
        /\ ~global_conn[conn].closed
        /\ num_fail < max_fail
        /\ num_fail' = num_fail + 1

        /\ expect_send' = [expect_send EXCEPT ![curr] = @ \o conn_val.send]
        /\ expect_recv' = [expect_recv EXCEPT ![curr] = @ \o conn_val.recv]

        /\ global_conn' = [global_conn EXCEPT
                ![conn].closed = TRUE,
                ![conn].send = <<>>,
                ![conn].recv = <<>>
            ]
        /\ UNCHANGED <<core_num_fail>>
        /\ UNCHANGED server_vars
        /\ UNCHANGED client_vars
        /\ auto_update

---------------------------------------------------------------------------

TerminateCond ==
    /\ \A c \in Client:
        /\ client_conn[c] # nil
        /\ ~global_conn[client_conn[c]].closed
        /\ client_main_pc[c] = "WaitConnClosed"
        /\ client_send_pc[c] = "Sleep"
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
        \/ ClientWaitConnClosed(c)
        \/ ServerAcceptConn(c)

    \/ \E c \in Client, g \in Group, k \in Key, v \in Value:
        \/ ClientCreate(c, g, k, v)

    \/ \E c \in Client, g \in Group, k \in Key:
        \/ ClientChildren(c, g)

    \/ ServerHandleConnect
    \/ ServerHandleRequest
    \/ ServerRemoveActiveConn
    \/ ServerLoseSession

    \/ ConnectionClosed
    \/ Terminated

Spec == Init /\ [][Next]_vars

---------------------------------------------------------------------------

CoreInv == ZK!Spec

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


RecvMapKeyRangeInv ==
    \A c \in Client:
        LET d == DOMAIN recv_map[c] IN
            d # {} => d = minOf(d)..maxOf(d)


ConnClosedMustEmpty ==
    \A conn \in DOMAIN global_conn:
        global_conn[conn].closed =>
            /\ global_conn[conn].send = <<>>
            /\ global_conn[conn].recv = <<>>


SendQueueMustEmptyWhenNotHasSession ==
    \A c \in Client:
        client_status[c] # "HasSession" => send_queue[c] = <<>>


ConnNotInAnyClientMustClosed ==
    \A conn \in DOMAIN global_conn:
        LET
            exist_client ==
                \E c \in Client: client_conn[c] = conn
        IN
            ~exist_client => global_conn[conn].closed


\* TODO Check Server Active Connections on single Session

====

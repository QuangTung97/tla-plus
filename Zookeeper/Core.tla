------ MODULE Core ----
EXTENDS TLC, FiniteSets, Sequences, Naturals, Common

CONSTANTS Group, Key, Value, Client, nil,
    value_range, max_action

ASSUME IsFiniteSet(Group)

VARIABLES server_log, server_state,
    client_status, client_req,
    recv_req, handle_req, num_action

server_vars == <<server_log, server_state>>
client_vars == <<
    client_status, client_req,
    recv_req, handle_req, num_action
>>
vars == <<server_vars, client_vars>>

---------------------------------------------------------------------------

Session == 11..(10 + value_range)
Zxid == 21..(20 + value_range)

NullSession == Session \union {nil}
NullZxid == Zxid \union {nil}
NullValue == Value \union {nil}

LogEntry ==
    LET
        new_sess == [
            type: {"NewSession"},
            zxid: Zxid,
            sess: Session
        ]

        put_entry == [
            type: {"Put"},
            zxid: Zxid,
            group: Group,
            key: Key,
            val: NullValue
        ]
    IN
        UNION {new_sess, put_entry}

StateInfo == [
    val: NullValue,
    sess: NullSession \* NULL = Ephemeral ZNode
]

new_state_info(val) == [
    val |-> val,
    sess |-> nil
]

ClientRequest ==
    LET
        connect_req == [
            type: {"Connect"},
            sess: NullSession
        ]

        create_req == [
            type: {"Create"},
            group: Group,
            key: Key,
            val: NullValue
        ]

        children_req == [
            type: {"Children"},
            group: Group
        ]
    IN
        UNION {connect_req, create_req, children_req}

HandleResponse ==
    LET
        children == [
            children: SUBSET Key
        ]
    IN
    UNION {children}

HandleRequest ==
    LET
        new_sess == [
            type: {"ConnectReply"},
            sess: NullSession
        ]

        normal == [
            req: ClientRequest,
            zxid: NullZxid,
            resp: HandleResponse \union {nil},
            status: {"OK", "NetErr", "Existed"}
        ]
    IN
        UNION {new_sess, normal}

new_handle_req(req, zxid, status) == [
    req |-> req,
    zxid |-> zxid,
    resp |-> nil,
    status |-> status
]

new_handle_with_resp(req, zxid, resp, status) == [
    req |-> req,
    zxid |-> zxid,
    resp |-> resp,
    status |-> status
]


---------------------------------------------------------------------------

CheckTypeOK ==
    /\ server_log \in Seq(LogEntry)

TypeOK ==
    /\ server_log \in Seq(LogEntry)
    /\ DOMAIN server_state = Group
    /\ \A g \in Group: IsMapOf(server_state[g], Key, StateInfo)

    /\ client_status \in [Client -> {"Disconnected", "Connecting", "HasSession"}]
    /\ client_req \in [Client -> Seq(ClientRequest)]
    /\ recv_req \in [Client -> Seq(HandleRequest)]
    /\ handle_req \in [Client -> Seq(HandleRequest)]
    /\ num_action \in 0..max_action

Init ==
    /\ server_log = <<>>
    /\ server_state = [g \in Group |-> <<>>]

    /\ client_status = [c \in Client |-> "Disconnected"]
    /\ client_req = [c \in Client |-> <<>>]
    /\ recv_req = [c \in Client |-> <<>>]
    /\ handle_req = [c \in Client |-> <<>>]
    /\ num_action = 0

---------------------------------------------------------------------------

ClientConnect(c) ==
    LET
        req == [
            type |-> "Connect",
            sess |-> nil
        ]
    IN
    /\ client_status[c] = "Disconnected"
    /\ client_status' = [client_status EXCEPT ![c] = "Connecting"]
    /\ client_req' = [client_req EXCEPT ![c] = Append(@, req)]

    /\ UNCHANGED <<recv_req, handle_req>>
    /\ UNCHANGED num_action
    /\ UNCHANGED server_vars


ClientRecvConnect(c) ==
    LET
        req == recv_req[c][1]
    IN
    /\ client_status[c] = "Connecting"
    /\ recv_req[c] # <<>>
    /\ recv_req' = [recv_req EXCEPT ![c] = Tail(@)]
    /\ handle_req' = [handle_req EXCEPT ![c] = Append(@, req)]
    /\ client_status' = [client_status EXCEPT ![c] = "HasSession"]

    /\ UNCHANGED client_req
    /\ UNCHANGED num_action
    /\ UNCHANGED server_vars


ClientRecvToHandle(c) ==
    LET
        req == recv_req[c][1]
    IN
    /\ client_status[c] = "HasSession"
    /\ recv_req[c] # <<>>
    /\ recv_req' = [recv_req EXCEPT ![c] = Tail(@)]
    /\ handle_req' = [handle_req EXCEPT ![c] = Append(@, req)]

    /\ UNCHANGED client_status
    /\ UNCHANGED client_req
    /\ UNCHANGED num_action
    /\ UNCHANGED server_vars


submit_client_req(c, req) ==
    LET
        when_has_sess ==
            /\ client_req' = [client_req EXCEPT ![c] = Append(@, req)]
            /\ UNCHANGED handle_req

        hreq == new_handle_req(req, nil, "NetErr")

        when_not_has_sess ==
            /\ handle_req' = [handle_req EXCEPT ![c] = Append(@, hreq)]
            /\ UNCHANGED client_req
    IN
    /\ num_action < max_action
    /\ num_action' = num_action + 1
    /\ IF client_status[c] = "HasSession"
        THEN when_has_sess
        ELSE when_not_has_sess
    /\ UNCHANGED recv_req
    /\ UNCHANGED client_status
    /\ UNCHANGED server_vars


ClientCreate(c, g, k, val) ==
    LET
        req == [
            type |-> "Create",
            group |-> g,
            key |-> k,
            val |-> val
        ]
    IN
    /\ submit_client_req(c, req)


ClientChildren(c, g) ==
    LET
        req == [
            type |-> "Children",
            group |-> g
        ]
    IN
    /\ submit_client_req(c, req)


ClientHandleReq(c) ==
    /\ handle_req[c] # <<>>
    /\ handle_req' = [handle_req EXCEPT ![c] = Tail(@)]

    /\ UNCHANGED num_action
    /\ UNCHANGED <<client_req, recv_req>>
    /\ UNCHANGED client_status
    /\ UNCHANGED server_vars

---------------------------------------------------------------------------

new_zxid ==
    IF server_log = <<>>
        THEN 21
        ELSE server_log[Len(server_log)].zxid + 1

server_handle_unchanged ==
    /\ UNCHANGED handle_req
    /\ UNCHANGED client_status
    /\ UNCHANGED num_action

client_with_req(c, type) ==
    LET
        req == client_req[c][1]
    IN
    /\ client_req[c] # <<>>
    /\ req.type = type
    /\ client_req' = [client_req EXCEPT ![c] = Tail(@)]


ServerHandleConnect(c) ==
    LET
        req == client_req[c][1]

        is_new_sess(entry) == entry.type = "NewSession"

        new_sess_log == SelectSeq(server_log, is_new_sess)

        new_sess ==
            IF server_log = <<>>
                THEN 11
                ELSE new_sess_log[Len(new_sess_log)].sess + 1

        hreq == [
            type |-> "ConnectReply",
            sess |-> new_sess
        ]

        log_entry == [
            type |-> "NewSession",
            zxid |-> new_zxid,
            sess |-> new_sess
        ]
    IN
    /\ client_with_req(c, "Connect")

    /\ recv_req' = [recv_req EXCEPT ![c] = Append(@, hreq)]
    /\ server_log' = Append(server_log, log_entry)

    /\ UNCHANGED server_state
    /\ server_handle_unchanged


push_to_recv(c, hreq) ==
    /\ recv_req' = [recv_req EXCEPT ![c] = Append(@, hreq)]


ServerHandleCreate(c) ==
    LET
        req == client_req[c][1]
        g == req.group
        k == req.key
        val == req.val

        hreq == new_handle_req(req, new_zxid, "OK")

        log_entry == [
            type |-> "Put",
            zxid |-> new_zxid,
            group |-> g,
            key |-> k,
            val |-> val
        ]

        state == new_state_info(val)

        when_not_existed ==
            /\ push_to_recv(c, hreq)
            /\ server_log' = Append(server_log, log_entry)
            /\ server_state' = [server_state EXCEPT ![g] = mapPut(@, k, state)]

        err_hreq == new_handle_req(req, nil, "Existed")

        when_existed ==
            /\ push_to_recv(c, err_hreq)
            /\ UNCHANGED server_log
            /\ UNCHANGED server_state
    IN
    /\ client_with_req(c, "Create")
    /\ IF k \in DOMAIN server_state[g]
        THEN when_existed
        ELSE when_not_existed
    /\ server_handle_unchanged


ServerHandleChildren(c) ==
    LET
        req == client_req[c][1]
        g == req.group

        children == [
            children |-> DOMAIN server_state[g]
        ]

        hreq == new_handle_with_resp(req, new_zxid, children, "OK")
    IN
    /\ client_with_req(c, "Children")
    /\ push_to_recv(c, hreq)

    /\ UNCHANGED server_log
    /\ UNCHANGED server_state
    /\ server_handle_unchanged

---------------------------------------------------------------------------

StopCond ==
    /\ \A c \in Client:
        /\ client_req[c] = <<>>
        /\ recv_req[c] = <<>>
        /\ handle_req[c] = <<>>

TerminateCond ==
    /\ StopCond

Terminated ==
    /\ TerminateCond
    /\ UNCHANGED vars

--------------------------------------------

RequiredNext ==
    \/ \E c \in Client:
        \/ ClientConnect(c)
        \/ ClientRecvConnect(c)
        \/ ClientRecvToHandle(c)

    \/ \E c \in Client:
        \/ ServerHandleConnect(c)
        \/ ServerHandleCreate(c)
        \/ ServerHandleChildren(c)

    \/ \E c \in Client, g \in Group, k \in Key, val \in NullValue:
        \/ ClientCreate(c, g, k, val)

    \/ \E c \in Client, g \in Group:
        \/ ClientChildren(c, g)

Next ==
    \/ RequiredNext
    \/ \E c \in Client: ClientHandleReq(c)
    \/ Terminated

Spec == Init /\ [][Next]_vars

---------------------------------------------------------------------------

ServerLogZxidInv ==
    LET
        n == Len(server_log) - 1
    IN
    \A i \in 1..n:
        server_log[i].zxid + 1 = server_log[i + 1].zxid


ReverseInvForChildren ==
    LET
        pre_cond(req) ==
            /\ "resp" \in DOMAIN req
            /\ req.resp # nil
            /\ "children" \in DOMAIN req.resp

        cond(req) ==
            /\ req.resp.children = {}
    IN
    \A c \in Client: \A i \in DOMAIN handle_req[c]:
        LET req == handle_req[c][i] IN
            pre_cond(req) => cond(req)


ReverseInv ==
    /\ TRUE

====

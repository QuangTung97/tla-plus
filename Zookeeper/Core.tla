------ MODULE Core ----
EXTENDS TLC, FiniteSets, Sequences, Naturals, Common

CONSTANTS Group, Key, Value, Client, nil, max_pending

ASSUME IsFiniteSet(Group)

VARIABLES server_log, server_state,
    client_status, client_request

server_vars == <<server_log, server_state>>
client_vars == <<client_status, client_request>>
vars == <<server_vars, client_vars>>

---------------------------------------------------------------------------

Zxid == 21..29

NullZxid == Zxid \union {nil}

Xid == 30..39

Session == 11..19

NullSession == Session \union {nil}

NullValue == Value \union {nil}

LogEntry ==
    LET
        session_entry == [
            type: {"NewSession"},
            zxid: Zxid,
            sess: Session
        ]

        put_entry == [
            type: {"Put"},
            zxid: Zxid,
            group: Group,
            key: Key,
            val: Value
        ]
    IN
        UNION {session_entry, put_entry}

StateInfo == [
    val: Value,
    sess: NullSession \* For Ephemeral ZNodes
]

ClientRequest ==
    LET
        create_req == [
            type: {"Create"},
            group: Group,
            key: Key,
            val: NullValue
        ]
    IN
        UNION {create_req}

---------------------------------------------------------------------------

TypeOK ==
    /\ server_log \in Seq(LogEntry)
    /\ DOMAIN server_state = Group
    /\ \A g \in Group: IsMapOf(server_state[g], Key, StateInfo)

    /\ client_status \in [Client -> {"Init", "HasSession"}]
    /\ client_request \in [Client -> Seq(ClientRequest)]

Init ==
    /\ server_log = <<>>
    /\ server_state = [g \in Group |-> <<>>]

    /\ client_status = [c \in Client |-> "Init"]
    /\ client_request = [c \in Client |-> <<>>]

---------------------------------------------------------------------------

ClientCreate(c, g, k, val) ==
    LET
        req == [
            type |-> "Create",
            group |-> g,
            key |-> k,
            val |-> val
        ]
    IN
    /\ Len(client_request[c]) < max_pending
    /\ client_request' = [client_request EXCEPT ![c] = Append(@, req)]

    /\ UNCHANGED client_status
    /\ UNCHANGED server_vars

---------------------------------------------------------------------------

StopCond ==
    /\ \A c \in Client: client_request[c] = <<>>

TerminateCond ==
    /\ StopCond

Terminated ==
    /\ TerminateCond
    /\ UNCHANGED vars


Next ==
    \/ \E c \in Client, g \in Group, k \in Key, val \in NullValue:
        \/ ClientCreate(c, g, k, val)
    \/ Terminated

Spec == Init /\ [][Next]_vars

---------------------------------------------------------------------------

ClientRequestLimit ==
    \A c \in Client: Len(client_request[c]) <= max_pending

====

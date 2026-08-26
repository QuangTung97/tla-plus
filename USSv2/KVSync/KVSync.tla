---- MODULE KVSync ----
EXTENDS TLC, Naturals, Sequences, FiniteSets

CONSTANTS Node, Key, Value, Conn, nil

VARIABLES
    state, conn_state,
    src_pc, src_local_conn, channel,
    dst_pc, sync_state,
    stop_update

src_vars == <<
    src_pc, src_local_conn, channel
>>

dst_vars == <<
    dst_pc, sync_state
>>

node_vars == <<
    src_vars, dst_vars
>>

aux_vars == <<
    stop_update
>>

vars == <<
    state, conn_state,
    node_vars,
    aux_vars
>>

---------------------------------------------------------------

Null(S) == S \union {nil}

---------------------------------------------------------------

StateStore == [Key -> Null(Value)]

init_state_store == [k \in Key |-> nil]

SrcPC == {"Init", "RegisterWatcher", "WaitOnChan"}

DstPC == {"Init"}

ConnState == [
    client_closed: BOOLEAN,
    server_closed: BOOLEAN
]

Channel == [
    closed: BOOLEAN
]

---------------------------------------------------------------

TypeOK ==
    /\ state \in StateStore
    /\ conn_state \in [Conn -> Null(ConnState)]

    /\ src_pc \in [Node -> SrcPC]
    /\ src_local_conn \in [Node -> Null(Conn)]
    /\ channel \in [Conn -> Null(Channel)]

    /\ dst_pc \in [Node -> DstPC]
    /\ sync_state \in [Node -> StateStore]

    /\ stop_update \in BOOLEAN

Init ==
    /\ state = init_state_store
    /\ conn_state = [c \in Conn |-> nil]

    /\ src_pc = [n \in Node |-> "Init"]
    /\ src_local_conn = [n \in Node |-> nil]
    /\ channel = [c \in Conn |-> nil]

    /\ dst_pc = [n \in Node |-> "Init"]
    /\ sync_state = [n \in Node |-> init_state_store]

    /\ stop_update = FALSE

---------------------------------------------------------------

UpdateKV(k, v) ==
    /\ ~stop_update

    /\ state[k] # v
    /\ state' = [state EXCEPT ![k] = v]

    /\ UNCHANGED conn_state
    /\ UNCHANGED node_vars
    /\ UNCHANGED aux_vars

---------------------------------------------------------------

set_local(var, k, x) ==
    var' = [var EXCEPT ![k] = x]

src_goto(n, l) ==
    set_local(src_pc, n, l)

---------------------------------------------------------------

src_action_unchanged ==
    /\ UNCHANGED state
    /\ UNCHANGED dst_vars
    /\ UNCHANGED aux_vars

---------------------------------------------------------------

NewConn(n, c) ==
    LET
        new_conn == [
            client_closed |-> FALSE,
            server_closed |-> FALSE
        ]
    IN
    /\ src_pc[n] = "Init"
    /\ conn_state[c] = nil

    /\ src_goto(n, "RegisterWatcher")
    /\ set_local(conn_state, c, new_conn)
    /\ set_local(src_local_conn, n, c)

    /\ UNCHANGED channel
    /\ src_action_unchanged

---------------------------------------------------------------

RegisterWatcher(n) ==
    LET
        c == src_local_conn[n]

        new_chan == [
            closed |-> FALSE
        ]
    IN
    /\ src_pc[n] = "RegisterWatcher"

    /\ src_goto(n, "WaitOnChan")
    /\ set_local(channel, c, new_chan)

    /\ UNCHANGED conn_state
    /\ UNCHANGED src_local_conn
    /\ src_action_unchanged

---------------------------------------------------------------

StopUpdate ==
    /\ ~stop_update
    /\ stop_update' = TRUE

    /\ UNCHANGED state
    /\ UNCHANGED conn_state
    /\ UNCHANGED node_vars

---------------------------------------------------------------

StopCond ==
    /\ \A n \in Node:
        /\ src_pc[n] = "WaitOnChan"

TerminateCond ==
    /\ stop_update
    /\ StopCond

Terminated ==
    /\ TerminateCond
    /\ UNCHANGED vars

---------------------------------------------------------------

Next ==
    \/ \E k \in Key, v \in Null(Value):
        \/ UpdateKV(k, v)
    \/ \E n \in Node, c \in Conn:
        \/ NewConn(n, c)
    \/ \E n \in Node:
        \/ RegisterWatcher(n)
    \/ StopUpdate
    \/ Terminated

Spec == Init /\ [][Next]_vars

---------------------------------------------------------------

StopCondInv ==
    StopCond =>
        \A n \in Node:
            state = sync_state[n]

====

---- MODULE KVSync ----
EXTENDS TLC, Naturals, Sequences, FiniteSets

CONSTANTS Node, Key, Value, Conn, nil, conn_buf_size

VARIABLES
    state, watch_list, channel, conn_sync_keys,
    conn_state,
    src_pc, src_local_conn,
    dst_pc, dst_local_conn, sync_state,
    key_list, stop_update

client_vars == <<
    state, watch_list, channel, conn_sync_keys
>>

src_vars == <<
    src_pc, src_local_conn
>>

dst_vars == <<
    dst_pc, dst_local_conn, sync_state
>>

node_vars == <<
    src_vars, dst_vars
>>

aux_vars == <<
    key_list, stop_update
>>

vars == <<
    client_vars,
    conn_state,
    node_vars,
    aux_vars
>>

---------------------------------------------------------------

Null(S) == S \union {nil}

-----------------------

PermSeq(S) ==
    LET
        n == Cardinality(S)
        domain == 1..n
        all_seqs == [domain -> S]

        cond(seq) ==
            \A i, j \in domain:
                seq[i] = seq[j] => i = j
    IN
        {s \in all_seqs: cond(s)}

ASSUME PermSeq({11, 12}) = {<<11, 12>>, <<12, 11>>}

---------------------------------------------------------------

StateStore == [Key -> Null(Value)]

init_state_store == [k \in Key |-> nil]

-----------------------

SrcPC == {"Init", "NewWatchChan", "SetWatchChan", "WaitOnChan"}

DstPC == {"Init", "ReadFromConn"}

-----------------------

Action ==
    LET
        put == [
            type: {"Put"},
            key: Key,
            value: Null(Value)
        ]
    IN
        UNION {put}

put_action(k, v) == [
    type |-> "Put",
    key |-> k,
    value |-> v
]

-----------------------

ConnState == [
    data: Seq(Action),
    client_closed: BOOLEAN,
    server_closed: BOOLEAN
]

-----------------------

Channel == [
    data: Seq(Action),
    closed: BOOLEAN
]

---------------------------------------------------------------

TypeOK ==
    /\ state \in StateStore
    /\ watch_list \subseteq Conn
    /\ channel \in [Conn -> Null(Channel)]
    /\ conn_sync_keys \in [Conn -> SUBSET Key]

    /\ conn_state \in [Conn -> Null(ConnState)]

    /\ src_pc \in [Node -> SrcPC]
    /\ src_local_conn \in [Node -> Null(Conn)]

    /\ dst_pc \in [Node -> DstPC]
    /\ dst_local_conn \in [Node -> Null(Conn)]
    /\ sync_state \in [Node -> StateStore]

    /\ key_list \in PermSeq(Key)
    /\ stop_update \in BOOLEAN

Init ==
    /\ state = init_state_store
    /\ watch_list = {}
    /\ conn_state = [c \in Conn |-> nil]
    /\ channel = [c \in Conn |-> nil]
    /\ conn_sync_keys = [c \in Conn |-> {}]

    /\ src_pc = [n \in Node |-> "Init"]
    /\ src_local_conn = [n \in Node |-> nil]

    /\ dst_pc = [n \in Node |-> "Init"]
    /\ dst_local_conn = [n \in Node |-> nil]
    /\ sync_state = [n \in Node |-> init_state_store]

    /\ key_list \in PermSeq(Key)
    /\ stop_update = FALSE

---------------------------------------------------------------

UpdateKV(k, v) ==
    LET
        update_channel(c, old) ==
            IF c \in watch_list THEN
                [old EXCEPT !.data = Append(@, put_action(k, v))]
            ELSE
                old

        update_sync_keys(c, old) ==
            IF conn_state[c] = nil THEN
                old
            ELSE IF c \in watch_list THEN
                old
            ELSE
                old \union {k}
    IN
    /\ ~stop_update

    /\ state[k] # v
    /\ state' = [state EXCEPT ![k] = v]
    /\ channel' = [c \in Conn |-> update_channel(c, channel[c])]
    /\ conn_sync_keys' = [
            c \in Conn |-> update_sync_keys(c, conn_sync_keys[c])
        ]
    /\ watch_list' = {}

    /\ UNCHANGED conn_state
    /\ UNCHANGED node_vars
    /\ UNCHANGED aux_vars

---------------------------------------------------------------

set_local(var, k, x) ==
    var' = [var EXCEPT ![k] = x]

src_goto(n, l) ==
    set_local(src_pc, n, l)

non_nil_keys ==
    {k \in Key: state[k] # nil}

---------------------------------------------------------------

src_action_unchanged ==
    /\ UNCHANGED state
    /\ UNCHANGED dst_vars
    /\ UNCHANGED aux_vars

---------------------------------------------------------------

NewConn(n, c) ==
    LET
        new_conn == [
            data |-> <<>>,
            client_closed |-> FALSE,
            server_closed |-> FALSE
        ]
    IN
    /\ src_pc[n] = "Init"
    /\ conn_state[c] = nil

    /\ src_goto(n, "NewWatchChan")
    /\ set_local(conn_state, c, new_conn)
    /\ set_local(src_local_conn, n, c)
    /\ set_local(conn_sync_keys, c, non_nil_keys)

    /\ UNCHANGED channel
    /\ UNCHANGED watch_list
    /\ src_action_unchanged

---------------------------------------------------------------

NewWatchChan(n) ==
    LET
        c == src_local_conn[n]

        empty_chan == [
            data |-> <<>>,
            closed |-> FALSE
        ]
    IN
    /\ src_pc[n] = "NewWatchChan"

    /\ src_goto(n, "SetWatchChan")
    /\ set_local(channel, c, empty_chan)

    /\ UNCHANGED watch_list
    /\ UNCHANGED conn_sync_keys
    /\ UNCHANGED conn_state
    /\ UNCHANGED src_local_conn
    /\ src_action_unchanged

---------------------------------------------------------------

SetWatchChan(n) ==
    LET
        c == src_local_conn[n]

        on_empty ==
            /\ watch_list' = watch_list \union {c}
            /\ UNCHANGED conn_sync_keys
            /\ UNCHANGED channel

        action(k) == put_action(k, state[k])

        on_non_empty(k) ==
            /\ conn_sync_keys' = [conn_sync_keys EXCEPT ![c] = @ \ {k} ]
            /\ channel' = [channel EXCEPT ![c].data = Append(@, action(k))]
            /\ UNCHANGED watch_list
    IN
    /\ src_pc[n] = "SetWatchChan"

    /\ src_goto(n, "WaitOnChan")
    /\ IF conn_sync_keys[c] = {}
        THEN on_empty
        ELSE \E k \in conn_sync_keys[c]: on_non_empty(k)

    /\ UNCHANGED src_local_conn
    /\ UNCHANGED conn_state
    /\ src_action_unchanged

---------------------------------------------------------------

WaitOnChan(n) ==
    LET
        c == src_local_conn[n]
        action == channel[c].data[1]
    IN
    /\ src_pc[n] = "WaitOnChan"
    /\ channel[c].data # <<>>

    /\ Len(conn_state[c].data) < conn_buf_size
    /\ channel' = [channel EXCEPT ![c].data = Tail(@)]
    /\ conn_state' = [conn_state EXCEPT ![c].data = Append(@, action)]
    /\ src_goto(n, "SetWatchChan")

    /\ UNCHANGED conn_sync_keys
    /\ UNCHANGED src_local_conn
    /\ UNCHANGED watch_list
    /\ src_action_unchanged

---------------------------------------------------------------

dst_goto(n, l) ==
    set_local(dst_pc, n, l)

dst_action_unchanged ==
    /\ UNCHANGED state
    /\ UNCHANGED client_vars
    /\ UNCHANGED src_vars
    /\ UNCHANGED aux_vars

---------------------------------------------------------------

StartServerConn(n) ==
    LET
        c == src_local_conn[n]
    IN
    /\ dst_pc[n] = "Init"
    /\ c # nil

    /\ set_local(dst_local_conn, n, c)
    /\ dst_goto(n, "ReadFromConn")

    /\ UNCHANGED sync_state
    /\ UNCHANGED conn_state
    /\ dst_action_unchanged

---------------------------------------------------------------

ReadFromConn(n) ==
    LET
        c == dst_local_conn[n]
        action == conn_state[c].data[1]
        k == action.key
        v == action.value
    IN
    /\ dst_pc[n] = "ReadFromConn"
    /\ conn_state[c].data # <<>>

    /\ conn_state' = [conn_state EXCEPT ![c].data = Tail(@)]
    /\ sync_state' = [sync_state EXCEPT ![n][k] = v]

    /\ UNCHANGED dst_local_conn
    /\ UNCHANGED dst_pc
    /\ dst_action_unchanged

---------------------------------------------------------------

StopUpdate ==
    /\ ~stop_update
    /\ stop_update' = TRUE

    /\ UNCHANGED key_list
    /\ UNCHANGED state
    /\ UNCHANGED conn_sync_keys
    /\ UNCHANGED watch_list
    /\ UNCHANGED channel
    /\ UNCHANGED conn_state
    /\ UNCHANGED node_vars

---------------------------------------------------------------

StopCond ==
    /\ \A n \in Node:
        /\ src_pc[n] = "WaitOnChan"
        /\ channel[src_local_conn[n]].data = <<>>
        /\ dst_pc[n] = "ReadFromConn"
    /\ \A c \in Conn:
        conn_state[c] # nil =>
            /\ conn_state[c].data = <<>>

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
        \/ NewWatchChan(n)
        \/ SetWatchChan(n)
        \/ WaitOnChan(n)
        \/ StartServerConn(n)
        \/ ReadFromConn(n)
    \/ StopUpdate
    \/ Terminated

Spec == Init /\ [][Next]_vars

---------------------------------------------------------------

StopCondInv ==
    StopCond =>
        \A n \in Node:
            state = sync_state[n]

-----------------------

ConnSyncKeysInv ==
    \A c \in Conn:
        /\ conn_state[c] = nil => conn_sync_keys[c] = {}

-----------------------

ChannelInv ==
    \A c \in Conn:
        /\ channel[c] # nil => Len(channel[c].data) <= 1
        /\ c \in watch_list =>
            /\ conn_state[c] # nil
            /\ Len(channel[c].data) = 0
            /\ conn_state[c] # nil
            /\ conn_sync_keys[c] = {}

-----------------------

ConnStateInv ==
    \A c \in Conn:
        conn_state[c] # nil =>
            Len(conn_state[c].data) <= conn_buf_size

====

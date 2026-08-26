---- MODULE KVSync ----
EXTENDS TLC, Naturals, Sequences, FiniteSets

CONSTANTS Node, Key, Value, Conn, nil

VARIABLES
    state, conn_state,
    src_pc, src_local_conn, channel, conn_sync_keys,
    dst_pc, sync_state,
    key_list, stop_update

src_vars == <<
    src_pc, src_local_conn, channel, conn_sync_keys
>>

dst_vars == <<
    dst_pc, sync_state
>>

node_vars == <<
    src_vars, dst_vars
>>

aux_vars == <<
    key_list, stop_update
>>

vars == <<
    state, conn_state,
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

SrcPC == {"Init", "RegisterWatcher", "WaitOnChan"}

DstPC == {"Init"}

-----------------------

Action ==
    LET
        put == [
            type: {"Put"},
            key: Key,
            value: Value
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
    /\ conn_state \in [Conn -> Null(ConnState)]

    /\ src_pc \in [Node -> SrcPC]
    /\ src_local_conn \in [Node -> Null(Conn)]
    /\ channel \in [Conn -> Null(Channel)]
    /\ conn_sync_keys \in [Conn -> SUBSET Key]

    /\ dst_pc \in [Node -> DstPC]
    /\ sync_state \in [Node -> StateStore]

    /\ key_list \in PermSeq(Key)
    /\ stop_update \in BOOLEAN

Init ==
    /\ state = init_state_store
    /\ conn_state = [c \in Conn |-> nil]

    /\ src_pc = [n \in Node |-> "Init"]
    /\ src_local_conn = [n \in Node |-> nil]
    /\ channel = [c \in Conn |-> nil]
    /\ conn_sync_keys = [c \in Conn |-> {}]

    /\ dst_pc = [n \in Node |-> "Init"]
    /\ sync_state = [n \in Node |-> init_state_store]

    /\ key_list \in PermSeq(Key)
    /\ stop_update = FALSE

---------------------------------------------------------------

UpdateKV(k, v) ==
    /\ ~stop_update

    /\ state[k] # v
    /\ state' = [state EXCEPT ![k] = v]
    /\ UNCHANGED conn_sync_keys \* TODO

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
    /\ UNCHANGED conn_sync_keys
    /\ src_action_unchanged

---------------------------------------------------------------

RegisterWatcher(n) ==
    LET
        c == src_local_conn[n]

        init_sync_keys == non_nil_keys

        empty_chan == [
            data |-> <<>>,
            closed |-> FALSE
        ]

        on_empty ==
            /\ set_local(channel, c, empty_chan)
            /\ set_local(conn_sync_keys, c, {})


        chan_data(k) == [empty_chan EXCEPT
            !.data = <<put_action(k, state[k])>>
        ]

        on_sync_key(k) ==
            /\ set_local(channel, c, chan_data(k))
            /\ set_local(conn_sync_keys, c, init_sync_keys \ {k})
    IN
    /\ src_pc[n] = "RegisterWatcher"

    /\ src_goto(n, "WaitOnChan")
    /\ IF init_sync_keys = {}
        THEN on_empty
        ELSE \E k \in init_sync_keys: on_sync_key(k)

    /\ UNCHANGED conn_state
    /\ UNCHANGED src_local_conn
    /\ src_action_unchanged

---------------------------------------------------------------

StopUpdate ==
    /\ ~stop_update
    /\ stop_update' = TRUE

    /\ UNCHANGED key_list
    /\ UNCHANGED state
    /\ UNCHANGED conn_state
    /\ UNCHANGED node_vars

---------------------------------------------------------------

StopCond ==
    /\ \A n \in Node:
        /\ src_pc[n] = "WaitOnChan"
        /\ channel[src_local_conn[n]].data = <<>>

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

-----------------------

ConnSyncKeysInv ==
    \A c \in Conn:
        /\ conn_state[c] = nil => conn_sync_keys[c] = {}
        /\ conn_sync_keys[c] \subseteq non_nil_keys

====

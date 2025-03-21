------ MODULE ConnPool ----
EXTENDS TLC, Naturals, Sequences, FiniteSets

CONSTANTS Node, nil, limit_num_conn

VARIABLES
    pc, next_conn, in_used, global_chan, wait_list,
    conn_pool, local_conn, local_chan, drop_conn, stop_cancel

vars == <<
    pc, next_conn, in_used, global_chan, wait_list,
    conn_pool, local_conn, local_chan, drop_conn, stop_cancel
>>

---------------------------------------------------------------------------------

DeleteSeq(s, index) ==
    LET
        n == Len(s) - 1
    IN
    [i \in 1..n |-> IF i < index THEN s[i] ELSE s[i + 1]]

ASSUME DeleteSeq(<<4, 5, 6>>, 1) = <<5, 6>>
ASSUME DeleteSeq(<<4, 5, 6>>, 2) = <<4, 6>>

Range(f) == {f[x]: x \in DOMAIN f}

---------------------------------------------------------------------------------

Conn == 20..29

NullConn == Conn \union {nil}

Status == {"OK"}

ChannelData == [
    data: Seq(Status)
]

Channel == DOMAIN global_chan

NullChannel == Channel \union {nil}

PC == {
    "Init", "NewConn", "UseConn",
    "WaitOnChan", "Terminated"
}

---------------------------------------------------------------------------------

TypeOK ==
    /\ pc \in [Node -> PC]
    /\ next_conn \in Conn
    /\ in_used \in Nat
    /\ global_chan \in Seq(ChannelData)
    /\ wait_list \in Seq(Channel)
    /\ conn_pool \in Seq(Conn)
    /\ local_conn \in [Node -> NullConn]
    /\ local_chan \in [Node -> NullChannel]
    /\ drop_conn \subseteq Conn
    /\ stop_cancel \in BOOLEAN

Init ==
    /\ pc = [n \in Node |-> "Init"]
    /\ next_conn = 20
    /\ in_used = 0
    /\ global_chan = <<>>
    /\ wait_list = <<>>
    /\ conn_pool = <<>>
    /\ local_conn = [n \in Node |-> nil]
    /\ local_chan = [n \in Node |-> nil]
    /\ drop_conn = {}
    /\ stop_cancel = FALSE

---------------------------------------------------------------------------------

goto(n, l) ==
    pc' = [pc EXCEPT ![n] = l]


GetConn(n) ==
    LET
        c == conn_pool[1]

        when_reuse ==
            /\ goto(n, "UseConn")
            /\ in_used' = in_used + 1
            /\ conn_pool' = Tail(conn_pool)
            /\ local_conn' = [local_conn EXCEPT ![n] = c]
            /\ UNCHANGED wait_list
            /\ UNCHANGED global_chan
            /\ UNCHANGED local_chan

        when_need_create ==
            /\ goto(n, "NewConn")
            /\ in_used' = in_used + 1
            /\ UNCHANGED wait_list
            /\ UNCHANGED conn_pool
            /\ UNCHANGED local_conn
            /\ UNCHANGED global_chan
            /\ UNCHANGED local_chan

        new_chan == [
            data |-> <<>>
        ]

        ch == Len(global_chan')

        when_reach_limit ==
            /\ goto(n, "WaitOnChan")
            /\ global_chan' = Append(global_chan, new_chan)
            /\ wait_list' = Append(wait_list, ch)
            /\ local_chan' = [local_chan EXCEPT ![n] = ch]
            /\ UNCHANGED in_used
            /\ UNCHANGED conn_pool
            /\ UNCHANGED local_conn
    IN
    /\ pc[n] = "Init"
    /\ IF Len(conn_pool) > 0 THEN
            when_reuse
        ELSE IF in_used < limit_num_conn THEN
            when_need_create
        ELSE
            when_reach_limit
    /\ UNCHANGED next_conn
    /\ UNCHANGED drop_conn
    /\ UNCHANGED stop_cancel


WaitOnChan(n) ==
    LET
        ch == local_chan[n]

        when_non_empty ==
            /\ global_chan[ch].data # <<>>
            /\ global_chan' = [global_chan EXCEPT ![ch].data = Tail(@)]
            /\ goto(n, "Init")
            /\ local_chan' = [local_chan EXCEPT ![n] = nil]

        when_ctx_cancel ==
            /\ ~stop_cancel
            /\ goto(n, "Terminated")
            /\ local_chan' = [local_chan EXCEPT ![n] = nil]
            /\ UNCHANGED global_chan
    IN
    /\ pc[n] = "WaitOnChan"
    /\ \/ when_non_empty
       \/ when_ctx_cancel
    /\ UNCHANGED wait_list
    /\ UNCHANGED conn_pool
    /\ UNCHANGED next_conn
    /\ UNCHANGED drop_conn
    /\ UNCHANGED in_used
    /\ UNCHANGED local_conn
    /\ UNCHANGED stop_cancel


NewConn(n) ==
    /\ pc[n] = "NewConn"
    /\ goto(n, "UseConn")
    /\ next_conn' = next_conn + 1
    /\ local_conn' = [local_conn EXCEPT ![n] = next_conn']
    /\ UNCHANGED in_used
    /\ UNCHANGED wait_list
    /\ UNCHANGED conn_pool
    /\ UNCHANGED drop_conn
    /\ UNCHANGED global_chan
    /\ UNCHANGED local_chan
    /\ UNCHANGED stop_cancel


notifyWaitList ==
    LET
        ch == wait_list[1]
    IN
    IF Len(wait_list) = 0
        THEN
            /\ UNCHANGED wait_list
            /\ UNCHANGED global_chan
        ELSE
            /\ wait_list' = Tail(wait_list)
            /\ global_chan' = [global_chan EXCEPT ![ch].data = Append(@, "OK")]

UseConn(n) ==
    LET
        when_normal ==
            /\ goto(n, "Terminated")
            /\ conn_pool' = Append(conn_pool, local_conn[n])
            /\ in_used' = in_used - 1
            /\ local_conn' = [local_conn EXCEPT ![n] = nil]
            /\ notifyWaitList
            /\ UNCHANGED drop_conn

        when_not_release ==
            /\ goto(n, "Terminated")
            /\ in_used' = in_used - 1
            /\ local_conn' = [local_conn EXCEPT ![n] = nil]
            /\ notifyWaitList
            /\ drop_conn' = drop_conn \union {local_conn[n]}
            /\ UNCHANGED conn_pool
    IN
    /\ pc[n] = "UseConn"
    /\ \/ when_normal
       \/ when_not_release
    /\ UNCHANGED next_conn
    /\ UNCHANGED local_chan
    /\ UNCHANGED stop_cancel


RemoveFromPool ==
    \E i \in DOMAIN conn_pool:
        /\ conn_pool' = DeleteSeq(conn_pool, i)
        /\ drop_conn' = drop_conn \union {conn_pool[i]}
        /\ UNCHANGED in_used
        /\ UNCHANGED local_conn
        /\ UNCHANGED next_conn
        /\ UNCHANGED pc
        /\ UNCHANGED wait_list
        /\ UNCHANGED global_chan
        /\ UNCHANGED local_chan
        /\ UNCHANGED stop_cancel


StopCancel ==
    /\ ~stop_cancel
    /\ stop_cancel' = TRUE
    /\ UNCHANGED conn_pool
    /\ UNCHANGED drop_conn
    /\ UNCHANGED in_used
    /\ UNCHANGED local_conn
    /\ UNCHANGED next_conn
    /\ UNCHANGED pc
    /\ UNCHANGED wait_list
    /\ UNCHANGED global_chan
    /\ UNCHANGED local_chan

---------------------------------------------------------------------------------

TerminateCond ==
    /\ \A n \in Node: pc[n] = "Terminated"

Terminated ==
    /\ TerminateCond
    /\ UNCHANGED vars


Next ==
    \/ \E n \in Node:
        \/ GetConn(n)
        \/ NewConn(n)
        \/ WaitOnChan(n)
        \/ UseConn(n)
    \/ RemoveFromPool
    \/ StopCancel
    \/ Terminated


Spec == Init /\ [][Next]_vars

FairSpec == Spec /\ WF_vars(Next)

---------------------------------------------------------------------------------

AlwaysTerminate == []<> TerminateCond

LimitConnInUse ==
    LET
        using_set == {n \in Node: pc[n] = "UseConn"}
    IN
        Cardinality(using_set) <= limit_num_conn


WhenTerminatedInv ==
    LET
        cmp_set == 21..next_conn \ drop_conn
    IN
    TerminateCond =>
        /\ in_used = 0
        /\ wait_list = <<>>
        /\ \A n \in Node:
            /\ local_conn[n] = nil
            /\ local_chan[n] = nil
        /\ Range(conn_pool) = cmp_set


EachConnAtMostOneUser ==
    \A c \in 21..next_conn:
        LET
            using_node == {n \in Node: pc[n] = "UseConn" /\ local_conn[n] = c}
        IN
            Cardinality(using_node) <= 1

====

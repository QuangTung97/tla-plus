------ MODULE ConnPool ----
EXTENDS TLC, Naturals, Sequences, FiniteSets

CONSTANTS Node, nil, limit_num_conn

VARIABLES
    pc, next_conn, in_used, wait_list,
    conn_pool, local_conn, drop_conn

vars == <<
    pc, next_conn, in_used, wait_list,
    conn_pool, local_conn, drop_conn
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

PC == {
    "Init", "NewConn", "UseConn",
    "WaitSignal", "Terminated"
}

---------------------------------------------------------------------------------

TypeOK ==
    /\ pc \in [Node -> PC]
    /\ next_conn \in Conn
    /\ in_used \in Nat
    /\ wait_list \in Seq(Node)
    /\ conn_pool \in Seq(Conn)
    /\ local_conn \in [Node -> NullConn]
    /\ drop_conn \subseteq Conn

Init ==
    /\ pc = [n \in Node |-> "Init"]
    /\ next_conn = 20
    /\ in_used = 0
    /\ wait_list = <<>>
    /\ conn_pool = <<>>
    /\ local_conn = [n \in Node |-> nil]
    /\ drop_conn = {}

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

        when_need_create ==
            /\ goto(n, "NewConn")
            /\ in_used' = in_used + 1
            /\ UNCHANGED wait_list
            /\ UNCHANGED conn_pool
            /\ UNCHANGED local_conn

        when_reach_limit ==
            /\ goto(n, "WaitSignal")
            /\ wait_list' = Append(wait_list, n)
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


NewConn(n) ==
    /\ pc[n] = "NewConn"
    /\ goto(n, "UseConn")
    /\ next_conn' = next_conn + 1
    /\ local_conn' = [local_conn EXCEPT ![n] = next_conn']
    /\ UNCHANGED in_used
    /\ UNCHANGED wait_list
    /\ UNCHANGED conn_pool
    /\ UNCHANGED drop_conn


notifyWaitList(new_pc) ==
    LET
        n == wait_list[1]
    IN
    IF Len(wait_list) = 0
        THEN
            /\ pc' = new_pc
            /\ UNCHANGED wait_list
        ELSE
            /\ wait_list' = Tail(wait_list)
            /\ pc' = [new_pc EXCEPT ![n] = "Init"]

UseConn(n) ==
    LET
        new_pc == [pc EXCEPT ![n] = "Terminated"]

        when_normal ==
            /\ conn_pool' = Append(conn_pool, local_conn[n])
            /\ in_used' = in_used - 1
            /\ local_conn' = [local_conn EXCEPT ![n] = nil]
            /\ notifyWaitList(new_pc)
            /\ UNCHANGED drop_conn

        when_not_release ==
            /\ in_used' = in_used - 1
            /\ local_conn' = [local_conn EXCEPT ![n] = nil]
            /\ notifyWaitList(new_pc)
            /\ drop_conn' = drop_conn \union {local_conn[n]}
            /\ UNCHANGED conn_pool
    IN
    /\ pc[n] = "UseConn"
    /\ \/ when_normal
       \/ when_not_release
    /\ UNCHANGED next_conn


RemoveFromPool ==
    \E i \in DOMAIN conn_pool:
        /\ conn_pool' = DeleteSeq(conn_pool, i)
        /\ drop_conn' = drop_conn \union {conn_pool[i]}
        /\ UNCHANGED in_used
        /\ UNCHANGED local_conn
        /\ UNCHANGED next_conn
        /\ UNCHANGED pc
        /\ UNCHANGED wait_list

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
        \/ UseConn(n)
    \/ RemoveFromPool
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
        /\ \A n \in Node: local_conn[n] = nil
        /\ Range(conn_pool) = cmp_set

====

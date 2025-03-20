------ MODULE ConnPool ----
EXTENDS TLC, Naturals, Sequences, FiniteSets

CONSTANTS Node, nil, limit_num_conn

VARIABLES
    pc, next_conn, in_used, wait_list,
    conn_pool, local_conn

vars == <<
    pc, next_conn, in_used, wait_list,
    conn_pool, local_conn
>>

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

Init ==
    /\ pc = [n \in Node |-> "Init"]
    /\ next_conn = 20
    /\ in_used = 0
    /\ wait_list = <<>>
    /\ conn_pool = <<>>
    /\ local_conn = [n \in Node |-> nil]

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


NewConn(n) ==
    /\ pc[n] = "NewConn"
    /\ goto(n, "UseConn")
    /\ next_conn' = next_conn + 1
    /\ local_conn' = [local_conn EXCEPT ![n] = next_conn']
    /\ UNCHANGED in_used
    /\ UNCHANGED wait_list
    /\ UNCHANGED conn_pool


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

        when_not_release ==
            /\ in_used' = in_used - 1
            /\ local_conn' = [local_conn EXCEPT ![n] = nil]
            /\ notifyWaitList(new_pc)
            /\ UNCHANGED conn_pool
    IN
    /\ pc[n] = "UseConn"
    /\ \/ when_normal
       \/ when_not_release
    /\ UNCHANGED next_conn


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
    TerminateCond =>
        /\ in_used = 0
        /\ wait_list = <<>>
        /\ \A n \in Node: local_conn[n] = nil

====

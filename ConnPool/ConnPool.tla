------ MODULE ConnPool ----
EXTENDS TLC, Naturals, Sequences

CONSTANTS Node, nil

VARIABLES pc, next_conn, conn_pool, local_conn

vars == <<pc, next_conn, conn_pool, local_conn>>

---------------------------------------------------------------------------------

Conn == 20..29

NullConn == Conn \union {nil}

PC == {"Init", "NewConn", "UseConn", "Terminated"}

---------------------------------------------------------------------------------

TypeOK ==
    /\ pc \in [Node -> PC]
    /\ next_conn \in Conn
    /\ conn_pool \in Seq(Conn)
    /\ local_conn \in [Node -> NullConn]

Init ==
    /\ pc = [n \in Node |-> "Init"]
    /\ next_conn = 20
    /\ conn_pool = <<>>
    /\ local_conn = [n \in Node |-> nil]

---------------------------------------------------------------------------------

goto(n, l) ==
    pc' = [pc EXCEPT ![n] = l]


GetConn(n) ==
    /\ pc[n] = "Init"
    /\ goto(n, "NewConn")
    /\ UNCHANGED next_conn
    /\ UNCHANGED conn_pool


NewConn(n) ==
    /\ pc[n] = "NewConn"
    /\ goto(n, "UseConn")
    /\ next_conn' = next_conn + 1
    /\ UNCHANGED conn_pool


UseConn(n) ==
    /\ pc[n] = "UseConn"
    /\ goto(n, "Terminated")
    /\ conn_pool' = Append(conn_pool, local_conn[n])

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

---------------------------------------------------------------------------------

====

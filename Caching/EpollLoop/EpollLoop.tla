---- MODULE EpollLoop ----
EXTENDS TLC, Sequences

CONSTANTS Worker, Conn, Value, nil

VARIABLES
    action_queue, conn_state,
    listen_pc, ready_conns, listen_local_conn, listen_local_worker,
    worker_pc, worker_conn

listen_vars == <<
    listen_pc, ready_conns, listen_local_conn, listen_local_worker
>>

worker_vars == <<worker_pc, worker_conn>>

vars == <<
    action_queue, conn_state,
    listen_vars,
    worker_vars
>>

------------------------------------------------------

Null(S) == S \union {nil}

Action ==
    LET
        new_conn == [
            type: {"NewConn"},
            conn: Conn
        ]
    IN
    UNION {new_conn}


ConnState == [
    send: Seq(Value),
    recv: Seq(Value),
    send_closed: BOOLEAN,
    recv_closed: BOOLEAN
]

WorkerPC == {"Init"}

------------------------------------------------------

TypeOK ==
    /\ action_queue \in [Worker -> Seq(Action)]
    /\ conn_state \in [Conn -> Null(ConnState)]

    /\ listen_pc \in {"Init", "PushNewConn", "IncEventFd"}
    /\ ready_conns \subseteq Conn
    /\ listen_local_conn \in Null(Conn)
    /\ listen_local_worker \in Null(Worker)

    /\ worker_pc \in [Worker -> WorkerPC]
    /\ worker_conn \in [Worker -> Null(Conn)]

Init ==
    /\ action_queue = [w \in Worker |-> <<>>]
    /\ conn_state = [c \in Conn |-> nil]

    /\ listen_pc = "Init"
    /\ ready_conns = {}
    /\ listen_local_conn = nil
    /\ listen_local_worker = nil

    /\ worker_pc = [w \in Worker |-> "Init"]
    /\ worker_conn = [w \in Worker |-> nil]


------------------------------------------------------

NewConn(c) ==
    LET
        state == [
            send |-> <<>>,
            recv |-> <<>>,
            send_closed |-> FALSE,
            recv_closed |-> FALSE
        ]
    IN
    /\ conn_state[c] = nil
    /\ ready_conns' = ready_conns \union {c}
    /\ conn_state' = [conn_state EXCEPT ![c] = state]
    /\ UNCHANGED action_queue
    /\ UNCHANGED worker_vars
    /\ UNCHANGED <<listen_pc, listen_local_conn, listen_local_worker>>

------------------------------------------------------

AcceptConn(c) ==
    /\ listen_pc = "Init"
    /\ c \in ready_conns

    /\ listen_pc' = "PushNewConn"
    /\ ready_conns' = ready_conns \ {c}
    /\ listen_local_conn' = c

    /\ UNCHANGED listen_local_worker
    /\ UNCHANGED action_queue
    /\ UNCHANGED conn_state
    /\ UNCHANGED worker_vars

------------------------------------------------------

PushNewConn(w) ==
    LET
        event == [
            type |-> "NewConn",
            conn |-> listen_local_conn
        ]
    IN
    /\ listen_pc = "PushNewConn"

    /\ listen_pc' = "IncEventFd"
    /\ action_queue' = [action_queue EXCEPT ![w] = Append(@, event)]
    /\ listen_local_worker' = w

    /\ UNCHANGED conn_state
    /\ UNCHANGED <<ready_conns, listen_local_conn>>
    /\ UNCHANGED worker_vars

------------------------------------------------------

TerminateCond ==
    /\ listen_pc = "Init"
    /\ ready_conns = {}

Terminated ==
    /\ TerminateCond
    /\ UNCHANGED vars

------------------------------------------------------

Next ==
    \/ \E c \in Conn:
        \/ NewConn(c)
        \/ AcceptConn(c)
    \/ \E w \in Worker:
        \/ PushNewConn(w)
    \/ Terminated

Spec == Init /\ [][Next]_vars

------------------------------------------------------

====

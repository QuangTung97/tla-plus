---- MODULE EpollLoop ----
EXTENDS TLC, Sequences, Naturals

CONSTANTS Worker, Conn, Value, nil

VARIABLES
    action_queue, conn_state, epoll_events, eventfd_num,
    listen_pc, ready_conns, listen_local_conn, listen_local_worker,
    worker_pc, worker_conn, worker_events,
    task_queue, current_task, need_dec_eventfd

listen_vars == <<
    listen_pc, ready_conns, listen_local_conn, listen_local_worker
>>

worker_vars == <<
    worker_pc, worker_conn, worker_events,
    task_queue, current_task, need_dec_eventfd
>>

vars == <<
    action_queue, conn_state, epoll_events, eventfd_num,
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
    recv_closed: BOOLEAN,
    worker: Null(Worker)
]

EpollEvent ==
    LET
        eventfd == [
            type: {"EventFd"}
        ]
    IN
    UNION {eventfd}

Task ==
    LET
        consume_action == [
            type: {"ConsumeAction"}
        ]
    IN
    UNION {consume_action}

WorkerPC == {
    "WaitOnEpoll", "HandleEpollEvent", "HandleTaskQueue",
    "ConsumeEventFd", "ConsumeActionQueue"
}

------------------------------------------------------

TypeOK ==
    /\ action_queue \in [Worker -> Seq(Action)]
    /\ conn_state \in [Conn -> Null(ConnState)]
    /\ epoll_events \in [Worker -> (SUBSET EpollEvent)]
    /\ eventfd_num \in [Worker -> Nat]

    /\ listen_pc \in {"Init", "PushNewConn", "IncEventFd"}
    /\ ready_conns \subseteq Conn
    /\ listen_local_conn \in Null(Conn)
    /\ listen_local_worker \in Null(Worker)

    /\ worker_pc \in [Worker -> WorkerPC]
    /\ worker_conn \in [Worker -> Null(Conn)]
    /\ worker_events \in [Worker -> (SUBSET EpollEvent)]
    /\ task_queue \in [Worker -> Seq(Task)]
    /\ current_task \in [Worker -> Null(Task)]
    /\ need_dec_eventfd \in [Worker -> Null(BOOLEAN)]

Init ==
    /\ action_queue = [w \in Worker |-> <<>>]
    /\ conn_state = [c \in Conn |-> nil]
    /\ epoll_events = [w \in Worker |-> {}]
    /\ eventfd_num = [w \in Worker |-> 0]

    /\ listen_pc = "Init"
    /\ ready_conns = {}
    /\ listen_local_conn = nil
    /\ listen_local_worker = nil

    /\ worker_pc = [w \in Worker |-> "WaitOnEpoll"]
    /\ worker_conn = [w \in Worker |-> nil]
    /\ worker_events = [w \in Worker |-> {}]
    /\ task_queue = [w \in Worker |-> <<>>]
    /\ current_task = [w \in Worker |-> nil]
    /\ need_dec_eventfd = [w \in Worker |-> nil]

------------------------------------------------------

NewConn(c) ==
    LET
        state == [
            send |-> <<>>,
            recv |-> <<>>,
            send_closed |-> FALSE,
            recv_closed |-> FALSE,
            worker |-> nil
        ]
    IN
    /\ conn_state[c] = nil
    /\ ready_conns' = ready_conns \union {c}
    /\ conn_state' = [conn_state EXCEPT ![c] = state]

    /\ UNCHANGED action_queue
    /\ UNCHANGED worker_vars
    /\ UNCHANGED <<epoll_events, eventfd_num>>
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
    /\ UNCHANGED <<epoll_events, eventfd_num>>

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
    /\ UNCHANGED <<epoll_events, eventfd_num>>

------------------------------------------------------

IncEventFd ==
    LET
        w == listen_local_worker

        event == [
            type |-> "EventFd"
        ]

        add_to_epoll ==
            /\ epoll_events' = [epoll_events EXCEPT ![w] = @ \union {event}]
    IN
    /\ listen_pc = "IncEventFd"
    /\ listen_pc' = "Init"

    /\ listen_local_conn' = nil
    /\ listen_local_worker' = nil

    /\ eventfd_num' = [eventfd_num EXCEPT ![w] = @ + 1]
    /\ IF eventfd_num[w] = 0
        THEN add_to_epoll
        ELSE UNCHANGED epoll_events

    /\ UNCHANGED ready_conns
    /\ UNCHANGED conn_state
    /\ UNCHANGED action_queue
    /\ UNCHANGED worker_vars

------------------------------------------------------

goto(w, l) ==
    worker_pc' = [worker_pc EXCEPT ![w] = l]

set_local(w, var, x) ==
    var' = [var EXCEPT ![w] = x]

------------------------------------------------------

waitConsumeEpollEvents(w, sub) ==
    /\ epoll_events' = [epoll_events EXCEPT ![w] = @ \ sub]
    /\ worker_events' = [worker_events EXCEPT ![w] = sub]
    /\ goto(w, "HandleEpollEvent")

WaitOnEpoll(w) ==
    /\ worker_pc[w] = "WaitOnEpoll"
    /\ epoll_events[w] # {}
    /\ \E sub \in (SUBSET epoll_events[w]):
        /\ sub # {}
        /\ waitConsumeEpollEvents(w, sub)

    /\ UNCHANGED current_task
    /\ UNCHANGED task_queue
    /\ UNCHANGED worker_conn
    /\ UNCHANGED eventfd_num
    /\ UNCHANGED action_queue
    /\ UNCHANGED need_dec_eventfd
    /\ UNCHANGED conn_state
    /\ UNCHANGED listen_vars

------------------------------------------------------

doHandleEpollEvent(w, ev) ==
    LET
        task == [
            type |-> "ConsumeAction"
        ]

        on_eventfd ==
            /\ ev.type = "EventFd"
            /\ task_queue' = [task_queue EXCEPT ![w] = Append(@, task)]
            /\ need_dec_eventfd' = [need_dec_eventfd EXCEPT ![w] = TRUE]
    IN
    /\ worker_events' = [worker_events EXCEPT ![w] = @ \ {ev}]
    /\ on_eventfd
    /\ UNCHANGED worker_pc

HandleEpollEvent(w) ==
    LET
        on_empty ==
            /\ goto(w, "HandleTaskQueue")
            /\ UNCHANGED worker_events
            /\ UNCHANGED task_queue
            /\ UNCHANGED need_dec_eventfd
    IN
    /\ worker_pc[w] = "HandleEpollEvent"
    /\ IF worker_events[w] = {} THEN
            on_empty
        ELSE
            \E ev \in worker_events[w]: doHandleEpollEvent(w, ev)

    /\ UNCHANGED current_task
    /\ UNCHANGED worker_conn
    /\ UNCHANGED conn_state
    /\ UNCHANGED epoll_events
    /\ UNCHANGED eventfd_num
    /\ UNCHANGED action_queue
    /\ UNCHANGED listen_vars

------------------------------------------------------

normal_handle_unchanged ==
    /\ UNCHANGED epoll_events
    /\ UNCHANGED worker_events
    /\ UNCHANGED listen_vars

handleTaskConsumeAction(w, task) ==
    /\ task.type = "ConsumeAction"
    /\ IF need_dec_eventfd[w]
        THEN goto(w, "ConsumeEventFd")
        ELSE goto(w, "ConsumeActionQueue")

HandleTaskQueue(w) ==
    LET
        on_empty ==
            /\ goto(w, "WaitOnEpoll")
            /\ UNCHANGED current_task
            /\ UNCHANGED task_queue

        task == task_queue[w][1]

        on_normal ==
            /\ task_queue' = [task_queue EXCEPT ![w] = Tail(@)]
            /\ current_task' = [current_task EXCEPT ![w] = task]
            /\ \/ handleTaskConsumeAction(w, task)
    IN
    /\ worker_pc[w] = "HandleTaskQueue"
    /\ IF task_queue[w] = <<>>
        THEN on_empty
        ELSE on_normal

    /\ UNCHANGED worker_conn
    /\ UNCHANGED need_dec_eventfd
    /\ UNCHANGED action_queue
    /\ UNCHANGED conn_state
    /\ UNCHANGED eventfd_num
    /\ normal_handle_unchanged

------------------------------------------------------

ConsumeEventFd(w) ==
    /\ worker_pc[w] = "ConsumeEventFd"

    /\ goto(w, "ConsumeActionQueue")
    /\ eventfd_num' = [eventfd_num EXCEPT ![w] = 0]
    /\ need_dec_eventfd' = [need_dec_eventfd EXCEPT ![w] = FALSE]

    /\ UNCHANGED current_task
    /\ UNCHANGED action_queue
    /\ UNCHANGED conn_state
    /\ UNCHANGED worker_conn
    /\ UNCHANGED task_queue
    /\ normal_handle_unchanged

------------------------------------------------------

handleNewConnAction(w, action) ==
    LET
        conn == action.conn
    IN
    /\ action.type = "NewConn"
    /\ worker_conn' = [worker_conn EXCEPT ![w] = conn]
    /\ conn_state' = [conn_state EXCEPT ![conn].worker = w]

-----------

ConsumeActionQueue(w) ==
    LET
        on_empty ==
            /\ set_local(w, need_dec_eventfd, nil)
            /\ UNCHANGED action_queue
            /\ UNCHANGED task_queue
            /\ UNCHANGED worker_conn
            /\ UNCHANGED conn_state

        action == action_queue[w][1]

        on_normal ==
            /\ action_queue' = [action_queue EXCEPT ![w] = Tail(@)]
            /\ task_queue' = [task_queue EXCEPT ![w] = Append(@, current_task[w])]
            /\ \/ handleNewConnAction(w, action)
            /\ UNCHANGED need_dec_eventfd
    IN
    /\ worker_pc[w] = "ConsumeActionQueue"
    /\ goto(w, "HandleTaskQueue")
    /\ set_local(w, current_task, nil)

    /\ IF action_queue[w] = <<>>
        THEN on_empty
        ELSE on_normal

    /\ UNCHANGED eventfd_num
    /\ normal_handle_unchanged

------------------------------------------------------

TerminateCond ==
    /\ listen_pc = "Init"
    /\ ready_conns = {}
    /\ \A w \in Worker:
        /\ worker_pc[w] = "WaitOnEpoll"
        /\ epoll_events[w] = {}
        /\ worker_events[w] = {}
        /\ eventfd_num[w] = 0
        /\ action_queue[w] = <<>>
        /\ task_queue[w] = <<>>
        /\ need_dec_eventfd[w] = nil
        /\ current_task[w] = nil

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
    \/ IncEventFd

    \/ \E w \in Worker:
        \/ WaitOnEpoll(w)
        \/ HandleEpollEvent(w)
        \/ HandleTaskQueue(w)
        \/ ConsumeEventFd(w)
        \/ ConsumeActionQueue(w)
    \/ Terminated

Spec == Init /\ [][Next]_vars

------------------------------------------------------

EpollWaitOnlyWhenTaskQueueEmpty ==
    \A w \in Worker:
        worker_pc[w] = "WaitOnEpoll" => task_queue[w] = <<>>

-----------

ConnStateMatchWorkerConn ==
    \A w \in Worker:
        worker_conn[w] # nil => conn_state[worker_conn[w]].worker = w

-----------

NeedDecEventFdInv ==
    \A w \in Worker:
        /\ worker_pc[w] = "ConsumeEventFd" => need_dec_eventfd[w]
        /\ worker_pc[w] = "ConsumeActionQueue" => ~need_dec_eventfd[w]

-----------

CurrentTaskInv ==
    \A w \in Worker:
        /\ worker_pc[w] = "HandleTaskQueue" => current_task[w] = nil

====

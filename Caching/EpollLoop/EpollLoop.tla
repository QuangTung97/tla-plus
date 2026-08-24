---- MODULE EpollLoop ----
EXTENDS TLC, Sequences, Naturals, FiniteSets

CONSTANTS Worker, Conn, Value, nil

VARIABLES
    action_queue, conn_state, epoll_events, eventfd_num,
    listen_pc, ready_conns, listen_local_conn, listen_local_worker,
    worker_pc, worker_events,
    task_queue, current_task, yield_queue, need_dec_eventfd

listen_vars == <<
    listen_pc, ready_conns, listen_local_conn, listen_local_worker
>>

worker_vars == <<
    worker_pc, worker_events,
    task_queue, current_task, yield_queue, need_dec_eventfd
>>

vars == <<
    action_queue, conn_state, epoll_events, eventfd_num,
    listen_vars,
    worker_vars
>>

------------------------------------------------------

SubSliceStart(S, pos) ==
    IF pos > Len(S)
        THEN <<>>
        ELSE SubSeq(S, pos, Len(S))

ASSUME SubSliceStart(<<11, 12, 13>>, 2) = <<12, 13>>
ASSUME SubSliceStart(<<11, 12, 13>>, 5) = <<>>

-----------

SubSliceEnd(S, pos) ==
    IF pos < 1
        THEN <<>>
        ELSE SubSeq(S, 1, pos)

ASSUME SubSliceEnd(<<11, 12, 13>>, 0) = <<>>
ASSUME SubSliceEnd(<<11, 12, 13>>, 2) = <<11, 12>>

-----------

Min2(a, b) ==
    IF a < b THEN a ELSE b

ASSUME Min2(11, 12) = 11
ASSUME Min2(13, 12) = 12

-----------

Range(f) == {f[x]: x \in DOMAIN f}

------------------------------------------------------

Null(S) == S \union {nil}

limit_send_buf == 2

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

    worker: Null(Worker),

    read_size: Null(Nat),
    tmp_buf: Seq(Value),
    read_buf: Seq(Value)
]

EpollEvent ==
    LET
        eventfd == [
            type: {"EventFd"}
        ]

        epollin == [
            type: {"EPOLLIN"},
            conn: Conn
        ]
    IN
    UNION {eventfd, epollin}

Task ==
    LET
        consume_action == [
            type: {"ConsumeAction"}
        ]

        conn_read == [
            type: {"Read"},
            conn: Conn
        ]
    IN
    UNION {consume_action, conn_read}

WorkerPC == {
    "WaitOnEpoll", "HandleEpollEvent", "HandleTaskQueue",
    "ConsumeEventFd", "ConsumeActionQueue",
    "WorkerConnRead", "MoveToReadBuf", "HandleReadBuf"
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
    /\ worker_events \in [Worker -> (SUBSET EpollEvent)]
    /\ task_queue \in [Worker -> Seq(Task)]
    /\ current_task \in [Worker -> Null(Task)]
    /\ yield_queue \in [Worker -> Seq(Task)]
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
    /\ worker_events = [w \in Worker |-> {}]
    /\ task_queue = [w \in Worker |-> <<>>]
    /\ current_task = [w \in Worker |-> nil]
    /\ yield_queue = [w \in Worker |-> <<>>]
    /\ need_dec_eventfd = [w \in Worker |-> nil]

------------------------------------------------------

NewConn(c) ==
    LET
        state == [
            send |-> <<>>,
            recv |-> <<>>,
            send_closed |-> FALSE,
            recv_closed |-> FALSE,
            worker |-> nil,
            read_size |-> nil,
            tmp_buf |-> <<>>,
            read_buf |-> <<>>
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
    /\ UNCHANGED yield_queue
    /\ UNCHANGED eventfd_num
    /\ UNCHANGED action_queue
    /\ UNCHANGED need_dec_eventfd
    /\ UNCHANGED conn_state
    /\ UNCHANGED listen_vars

------------------------------------------------------

add_task_queue(w, task) ==
    task_queue' = [task_queue EXCEPT ![w] = Append(@, task)]

add_yield_queue(w, task) ==
    yield_queue' = [yield_queue EXCEPT ![w] = Append(@, task)]

-----------

onEpollEventFd(w, ev) ==
    LET
        task == [
            type |-> "ConsumeAction"
        ]
    IN
    /\ ev.type = "EventFd"
    /\ add_task_queue(w, task)
    /\ need_dec_eventfd' = [need_dec_eventfd EXCEPT ![w] = TRUE]

-----------

onEpollEventEPOLLIN(w, ev) ==
    LET
        task == [
            type |-> "Read",
            conn |-> ev.conn
        ]
    IN
    /\ ev.type = "EPOLLIN"
    /\ add_task_queue(w, task)
    /\ UNCHANGED need_dec_eventfd

-----------

doHandleEpollEvent(w, ev) ==
    /\ worker_events' = [worker_events EXCEPT ![w] = @ \ {ev}]
    /\ \/ onEpollEventFd(w, ev)
       \/ onEpollEventEPOLLIN(w, ev)
    /\ UNCHANGED worker_pc

HandleEpollEvent(w) ==
    LET
        on_empty ==
            /\ goto(w, "HandleTaskQueue") \* TODO update
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
    /\ UNCHANGED yield_queue
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

-----------

handleTaskConsumeAction(w, task) ==
    /\ task.type = "ConsumeAction"
    /\ IF need_dec_eventfd[w]
        THEN goto(w, "ConsumeEventFd")
        ELSE goto(w, "ConsumeActionQueue")

-----------

handleTaskReadConn(w, task) ==
    LET
        c == task.conn
        state == conn_state[c]
    IN
    /\ task.type = "Read"
    /\ IF Len(state.tmp_buf) = 0
        THEN goto(w, "WorkerConnRead")
        ELSE goto(w, "MoveToReadBuf")

-----------

HandleTaskQueue(w) ==
    LET
        on_empty ==
            /\ goto(w, "WaitOnEpoll")
            /\ UNCHANGED current_task
            /\ UNCHANGED task_queue

        task == task_queue[w][1]

        on_normal ==
            /\ task_queue' = [task_queue EXCEPT ![w] = Tail(@)]
            /\ set_local(w, current_task, task)
            /\ \/ handleTaskConsumeAction(w, task)
               \/ handleTaskReadConn(w, task)
    IN
    /\ worker_pc[w] = "HandleTaskQueue"
    /\ IF task_queue[w] = <<>>
        THEN on_empty
        ELSE on_normal

    /\ UNCHANGED yield_queue
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
    /\ UNCHANGED yield_queue
    /\ UNCHANGED conn_state
    /\ UNCHANGED task_queue
    /\ normal_handle_unchanged

------------------------------------------------------

handleNewConnAction(w, action) ==
    LET
        conn == action.conn

        init_conn(size) ==
            conn_state' = [conn_state EXCEPT
                ![conn].worker = w,
                ![conn].read_size = size
            ]
    IN
    /\ action.type = "NewConn"
    /\ \E size \in 1..limit_send_buf:
            init_conn(size)

-----------

ConsumeActionQueue(w) ==
    LET
        on_empty ==
            /\ set_local(w, need_dec_eventfd, nil)
            /\ UNCHANGED action_queue
            /\ UNCHANGED task_queue
            /\ UNCHANGED conn_state

        action == action_queue[w][1]

        on_normal ==
            /\ action_queue' = [action_queue EXCEPT ![w] = Tail(@)]
            /\ add_task_queue(w, current_task[w])
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
    /\ UNCHANGED yield_queue
    /\ normal_handle_unchanged

------------------------------------------------------

worker_conn_read_unchanged ==
    /\ UNCHANGED action_queue
    /\ UNCHANGED need_dec_eventfd
    /\ UNCHANGED eventfd_num
    /\ normal_handle_unchanged

------------------------------------------------------

WorkerConnRead(w) ==
    LET
        c == current_task[w].conn
        data == conn_state[c].send

        on_empty ==
            /\ goto(w, "HandleTaskQueue")
            /\ set_local(w, current_task, nil)
            /\ UNCHANGED conn_state

        on_normal ==
            /\ goto(w, "MoveToReadBuf")
            /\ conn_state' = [conn_state EXCEPT
                    ![c].send = <<>>,
                    ![c].tmp_buf = data
                ]
            /\ UNCHANGED current_task
    IN
    /\ worker_pc[w] = "WorkerConnRead"

    /\ IF data = <<>>
        THEN on_empty
        ELSE on_normal

    /\ UNCHANGED task_queue
    /\ UNCHANGED yield_queue
    /\ worker_conn_read_unchanged

------------------------------------------------------

add_back_task_queue(w) ==
    /\ goto(w, "HandleTaskQueue")
    /\ set_local(w, current_task, nil)
    /\ add_task_queue(w, current_task[w])

MoveToReadBuf(w) ==
    LET
        c == current_task[w].conn
        state == conn_state[c]

        remain == state.read_size - Len(state.read_buf)
        n == Min2(Len(state.tmp_buf), remain)

        new_tmp_buf == SubSliceStart(state.tmp_buf, n + 1)
        append_data == SubSliceEnd(state.tmp_buf, n)

        on_full ==
            /\ goto(w, "HandleReadBuf")
            /\ UNCHANGED task_queue
            /\ UNCHANGED current_task

        on_not_full ==
            /\ add_back_task_queue(w)
    IN
    /\ worker_pc[w] = "MoveToReadBuf"

    /\ conn_state' = [conn_state EXCEPT
            ![c].tmp_buf = new_tmp_buf,
            ![c].read_buf = @ \o append_data
        ]

    /\ IF n + Len(state.read_buf) = state.read_size
        THEN on_full
        ELSE on_not_full

    /\ UNCHANGED yield_queue
    /\ worker_conn_read_unchanged

------------------------------------------------------

add_to_yield_queue(w) ==
    /\ goto(w, "HandleTaskQueue")
    /\ set_local(w, current_task, nil)
    /\ add_yield_queue(w, current_task[w])

HandleReadBuf(w) ==
    LET
        task == current_task[w]
        c == task.conn

        when_normal ==
            /\ add_back_task_queue(w)
            /\ UNCHANGED yield_queue

        when_yield ==
            /\ add_to_yield_queue(w)
            /\ UNCHANGED task_queue
    IN
    /\ worker_pc[w] = "HandleReadBuf"

    /\ conn_state' = [conn_state EXCEPT ![c].read_buf = <<>>]
    /\ \/ when_normal
       \/ when_yield

    /\ worker_conn_read_unchanged

------------------------------------------------------

add_epoll_event(w, event) ==
    epoll_events' = [epoll_events EXCEPT ![w] = @ \union {event}]

conn_unchanged ==
    /\ UNCHANGED listen_vars
    /\ UNCHANGED action_queue
    /\ UNCHANGED eventfd_num
    /\ UNCHANGED worker_vars

ConnSend(c) ==
    LET
        w == conn_state[c].worker

        trigger_epoll_cond ==
            /\ conn_state[c].send = <<>>
            /\ w # nil

        event == [
            type |-> "EPOLLIN",
            conn |-> c
        ]
    IN
    /\ conn_state[c] # nil
    /\ Len(conn_state[c].send) < limit_send_buf

    /\ \E v \in Value:
        conn_state' = [conn_state EXCEPT ![c].send = Append(@, v)]

    /\ IF trigger_epoll_cond
        THEN add_epoll_event(w, event)
        ELSE UNCHANGED epoll_events

    /\ conn_unchanged

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
        /\ yield_queue[w] = <<>>
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
        \/ WorkerConnRead(w)
        \/ MoveToReadBuf(w)
        \/ HandleReadBuf(w)

    \/ \E c \in Conn:
        \/ ConnSend(c)

    \/ Terminated

Spec == Init /\ [][Next]_vars

------------------------------------------------------

EpollWaitOnlyWhenTaskQueueEmpty ==
    \A w \in Worker:
        worker_pc[w] = "WaitOnEpoll" => task_queue[w] = <<>>

-----------

NeedDecEventFdInv ==
    \A w \in Worker:
        /\ worker_pc[w] = "ConsumeEventFd" => need_dec_eventfd[w]
        /\ worker_pc[w] = "ConsumeActionQueue" => ~need_dec_eventfd[w]

-----------

CurrentTaskInv ==
    \A w \in Worker:
        /\ worker_pc[w] = "HandleTaskQueue" => current_task[w] = nil

-----------

ConnReadSizeInv ==
    \A c \in Conn:
        LET
            cond ==
                conn_state[c].worker # nil <=> conn_state[c].read_size # nil
        IN
            conn_state[c] # nil => cond

-----------

ConnStateReadInfoInv ==
    \A c \in Conn:
        LET
            state == conn_state[c]

            pre_cond ==
                /\ state # nil
                /\ state.worker # nil

            cond ==
                /\ Len(state.send) <= limit_send_buf
                /\ Len(state.tmp_buf) <= limit_send_buf
                /\ Len(state.read_buf) <= limit_send_buf
                /\ Len(state.read_buf) <= state.read_size
        IN
            pre_cond => cond

-----------

WorkerConnStateInv ==
    \A w \in Worker:
        LET
            c == current_task[w].conn
            state == conn_state[c]
        IN
        /\ worker_pc[w] = "WorkerConnRead" =>
            /\ state.tmp_buf = <<>>
        /\ worker_pc[w] = "HandleReadBuf" =>
            /\ Len(state.read_buf) = state.read_size
        /\ worker_pc[w] = "MoveToReadBuf" =>
            /\ state.tmp_buf # <<>>

-----------

TaskQueueNotDuplicated ==
    \A w \in Worker:
        Cardinality(Range(task_queue[w])) = Len(task_queue[w])

====

---- MODULE BuildMapping ----
EXTENDS TLC, Sequences, Naturals

CONSTANTS Workspace, Value, nil, max_restart

VARIABLES
    pc, timestamp, last_bazel_pid, workspace_pid,
    workspace_ts, socket_queue,
    workspace_value,
    god_ws_pid, god_ws_value,
    num_restart

vars == <<
    pc, timestamp, last_bazel_pid, workspace_pid,
    workspace_ts, socket_queue,
    workspace_value,
    god_ws_pid, god_ws_value,
    num_restart
>>

----------------------------------------------------------------------

Null(S) == S \union {nil}

Timestamp == 20..29

BazelPID == 30..39

PC == {"Init", "Build", "RunCmd", "GetBazelPID", "Terminated"}

QueueEntry == [
    pid: BazelPID,
    value: Value
]

----------------------------------------------------------------------

TypeOK ==
    /\ pc \in [Workspace -> PC]
    /\ timestamp \in Timestamp
    /\ last_bazel_pid \in BazelPID
    /\ workspace_pid \in [Workspace -> Null(BazelPID)]
    /\ workspace_ts \in [Workspace -> Null(Timestamp)]
    /\ socket_queue \in Seq(QueueEntry)
    /\ workspace_value \in [Workspace -> Null(Value)]

    /\ god_ws_pid \in [Workspace -> Null(BazelPID)]
    /\ god_ws_value \in [Workspace -> Null(Value)]
    /\ num_restart \in 0..max_restart

Init ==
    /\ pc = [w \in Workspace |-> "Init"]
    /\ timestamp = 20
    /\ last_bazel_pid = 30
    /\ workspace_pid = [w \in Workspace |-> nil]
    /\ workspace_ts = [w \in Workspace |-> nil]
    /\ socket_queue = <<>>
    /\ workspace_value = [w \in Workspace |-> nil]

    /\ god_ws_pid = [w \in Workspace |-> nil]
    /\ god_ws_value = [w \in Workspace |-> nil]
    /\ num_restart = 0

----------------------------------------------------------------------

goto(w, l) ==
    pc' = [pc EXCEPT ![w] = l]


StartBuild(w) ==
    /\ pc[w] = "Init"

    /\ goto(w, "Build")
    /\ timestamp' = timestamp + 1
    /\ workspace_ts' = [workspace_ts EXCEPT ![w] = timestamp']

    /\ UNCHANGED socket_queue
    /\ UNCHANGED last_bazel_pid
    /\ UNCHANGED workspace_pid
    /\ UNCHANGED god_ws_pid
    /\ UNCHANGED god_ws_value
    /\ UNCHANGED workspace_value
    /\ UNCHANGED num_restart

----------------------------------------------------------------------

BuildGen(w) ==
    LET
        when_new ==
            /\ last_bazel_pid' = last_bazel_pid + 1
            /\ god_ws_pid' = [god_ws_pid EXCEPT ![w] = last_bazel_pid']

        when_reuse ==
            /\ god_ws_pid[w] # nil
            /\ UNCHANGED last_bazel_pid
            /\ UNCHANGED god_ws_pid
    IN
    /\ pc[w] = "Build"

    /\ goto(w, "RunCmd")
    /\ \/ when_new
       \/ when_reuse

    /\ UNCHANGED workspace_pid
    /\ UNCHANGED timestamp
    /\ UNCHANGED workspace_ts
    /\ UNCHANGED socket_queue
    /\ UNCHANGED god_ws_value
    /\ UNCHANGED workspace_value
    /\ UNCHANGED num_restart

----------------------------------------------------------------------

RunCmd(w, v) ==
    LET
        entry == [
            pid |-> god_ws_pid[w],
            value |-> v
        ]
    IN
    /\ pc[w] = "RunCmd"
    /\ goto(w, "GetBazelPID")

    /\ socket_queue' = Append(socket_queue, entry)
    /\ god_ws_value' = [god_ws_value EXCEPT ![w] = v]

    /\ UNCHANGED workspace_pid
    /\ UNCHANGED timestamp
    /\ UNCHANGED last_bazel_pid
    /\ UNCHANGED god_ws_pid
    /\ UNCHANGED workspace_ts
    /\ UNCHANGED workspace_value
    /\ UNCHANGED num_restart

----------------------------------------------------------------------

GetBazelPID(w) ==
    /\ pc[w] = "GetBazelPID"
    /\ goto(w, "Terminated")

    /\ workspace_pid' = [workspace_pid EXCEPT ![w] = god_ws_pid[w]]

    /\ UNCHANGED socket_queue
    /\ UNCHANGED workspace_ts
    /\ UNCHANGED last_bazel_pid
    /\ UNCHANGED god_ws_pid
    /\ UNCHANGED god_ws_value
    /\ UNCHANGED timestamp
    /\ UNCHANGED workspace_value
    /\ UNCHANGED num_restart

----------------------------------------------------------------------

doConsumeQueue(w, e) ==
    /\ workspace_value' = [workspace_value EXCEPT ![w] = e.value]

    /\ UNCHANGED timestamp
    /\ UNCHANGED workspace_pid
    /\ UNCHANGED workspace_ts
    /\ UNCHANGED <<god_ws_pid, god_ws_value>>
    /\ UNCHANGED last_bazel_pid
    /\ UNCHANGED pc
    /\ UNCHANGED num_restart

ConsumeSocketQueue ==
    LET
        e == socket_queue[1]
    IN
    /\ Len(socket_queue) > 0
    /\ \E w \in Workspace:
        /\ workspace_pid[w] = e.pid
        /\ socket_queue' = Tail(socket_queue)
        /\ doConsumeQueue(w, e)

----------------------------------------------------------------------

socket_queue_empty(pid) ==
    {i \in DOMAIN socket_queue: socket_queue[i].pid = pid} = {}

StopCond(w) ==
    /\ pc[w] = "Terminated"
    /\ socket_queue_empty(workspace_pid[w])

----------------------------------------------------------------------

RestartBuild(w) ==
    /\ StopCond(w)
    /\ num_restart < max_restart
    /\ num_restart' = num_restart + 1
    /\ goto(w, "Init")

    /\ workspace_pid' = [workspace_pid EXCEPT ![w] = nil]
    /\ workspace_ts' = [workspace_ts EXCEPT ![w] = nil]
    /\ workspace_value' = [workspace_value EXCEPT ![w] = nil]

    /\ UNCHANGED timestamp
    /\ UNCHANGED socket_queue
    /\ UNCHANGED last_bazel_pid
    /\ UNCHANGED <<god_ws_pid, god_ws_value>>

----------------------------------------------------------------------

TerminateCond ==
    /\ \A w \in Workspace: StopCond(w)

Terminated ==
    /\ TerminateCond
    /\ UNCHANGED vars

---------------------------------------

Next ==
    \/ \E w \in Workspace:
        \/ StartBuild(w)
        \/ BuildGen(w)
        \/ \E v \in Value: RunCmd(w, v)
        \/ GetBazelPID(w)
        \/ RestartBuild(w)
    \/ ConsumeSocketQueue
    \/ Terminated

Spec == Init /\ [][Next]_vars

FairSpec == Spec /\ WF_vars(Next)

----------------------------------------------------------------------

AlwaysTerminated == []<>TerminateCond

GodMatchMemValue ==
    LET
        cond(w) ==
            god_ws_value[w] = workspace_value[w]
    IN
    \A w \in Workspace: StopCond(w) => cond(w)

====

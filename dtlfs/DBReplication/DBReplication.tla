---- MODULE DBReplication ----
EXTENDS TLC, Naturals, Sequences, FiniteSets

CONSTANTS Node, Value, nil, max_num_action

VARIABLES
    global_config,
    local_config, local_epoch, log,
    num_action,
    msgs

vars == <<
    global_config,
    local_config, local_epoch, log,
    num_action,
    msgs
>>

--------------------------------------------------------------

NonEmpty(S) == (SUBSET S) \ {{}}

ASSUME NonEmpty({1, 2}) = {{1, 2}, {1}, {2}}

Null(S) == S \union {nil}

--------------------------------------------------------------

Epoch == 10..19

LogPos == 1..max_num_action

----------------------

Config == [
    epoch: Epoch,
    isr: NonEmpty(Node),
    leader: Node
]

init_config(nodes, l) == [
    epoch |-> 10,
    isr |-> nodes,
    leader |-> l
]

----------------------

LogEntry == [
    epoch: Epoch,
    pos: LogPos,
    value: Value
]

----------------------

Msg ==
    LET
        send_req == [
            type: {"SendReq"},
            entry: LogEntry,
            recv: SUBSET Node
        ]
    IN
    UNION {send_req}

--------------------------------------------------------------

TypeOK ==
    /\ global_config \in Config

    /\ local_config \in [Node -> Null(Config)]
    /\ local_epoch \in [Node -> Null(Epoch)]
    /\ log \in [Node -> Seq(LogEntry)]
    /\ num_action \in 0..max_num_action

    /\ msgs \subseteq Msg

Init ==
    /\ \E nodes \in NonEmpty(Node): \E l \in nodes:
        /\ global_config = init_config(nodes, l)

    /\ local_config = [n \in Node |-> nil]
    /\ local_epoch = [n \in Node |-> nil]
    /\ log = [n \in Node |-> <<>>]
    /\ num_action = 0

    /\ msgs = {}

--------------------------------------------------------------

updateEpoch(n, epoch) ==
    IF local_epoch[n] # nil => local_epoch[n] < epoch THEN
        local_epoch' = [local_epoch EXCEPT ![n] = epoch]
    ELSE
        UNCHANGED local_epoch

acceptEpoch(n, epoch) ==
    /\ local_epoch[n] # nil => local_epoch[n] <= epoch
    /\ updateEpoch(n, epoch)

isLeader(n) ==
    /\ local_config[n] # nil
    /\ local_config[n].leader = n
    /\ local_config[n].epoch = global_config.epoch

allowAction ==
    /\ num_action < max_num_action
    /\ num_action' = num_action + 1

--------------------------------------------------------------

SyncConfig(n) ==
    LET
        epoch == global_config.epoch
    IN
    /\ local_config[n] # nil => local_config[n].epoch < epoch
    /\ local_config' = [local_config EXCEPT ![n] = global_config]
    /\ updateEpoch(n, epoch)

    /\ UNCHANGED num_action
    /\ UNCHANGED log
    /\ UNCHANGED global_config
    /\ UNCHANGED msgs

--------------------------------------------------------------

AddEntry(n, v) ==
    LET
        epoch == local_config[n].epoch

        pos == Len(log[n]) + 1

        entry == [
            epoch |-> epoch,
            pos |-> pos,
            value |-> v
        ]

        msg == [
            type |-> "SendReq",
            entry |-> entry,
            recv |-> local_config[n].isr \ {n}
        ]
    IN
    /\ isLeader(n)
    /\ allowAction

    /\ log' = [log EXCEPT ![n] = Append(@, entry)]
    /\ msgs' = msgs \union {msg}

    /\ UNCHANGED local_config
    /\ UNCHANGED local_epoch
    /\ UNCHANGED global_config

--------------------------------------------------------------

recvAcceptEntry(n, entry) ==
    LET
        pos == entry.pos
        highest_pos == Len(log[n])
    IN
    /\ pos = highest_pos + 1

doRecvEntry(n, req) ==
    LET
        epoch == req.entry.epoch
        pos == req.entry.pos
    IN
    /\ acceptEpoch(n, epoch)
    /\ recvAcceptEntry(n, req.entry)

    /\ log' = [log EXCEPT ![n] = Append(@, req.entry)]

    /\ UNCHANGED msgs
    /\ UNCHANGED global_config
    /\ UNCHANGED local_config
    /\ UNCHANGED num_action

RecvEntry(n) ==
    \E req \in msgs:
        /\ req.type = "SendReq"
        /\ n \in req.recv
        /\ doRecvEntry(n, req)

--------------------------------------------------------------

TerminateCond ==
    /\ FALSE

Terminated ==
    /\ TerminateCond
    /\ UNCHANGED vars

--------------------------------------------------------------

Next ==
    \/ \E n \in Node:
        \/ SyncConfig(n)
        \/ RecvEntry(n)
    \/ \E n \in Node, v \in Value:
        \/ AddEntry(n, v)
    \/ Terminated

Spec == Init /\ [][Next]_vars

--------------------------------------------------------------

====

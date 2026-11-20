---- MODULE DBReplication ----
EXTENDS TLC, Naturals, Sequences, FiniteSets

CONSTANTS Node, Value, nil, max_num_action

VARIABLES
    global_config,
    local_config, local_epoch, log,
    leader_pos_map, commit_pos,
    num_action,
    msgs

vars == <<
    global_config,
    local_config, local_epoch, log,
    leader_pos_map, commit_pos,
    num_action,
    msgs
>>

--------------------------------------------------------------

NonEmpty(S) == (SUBSET S) \ {{}}

ASSUME NonEmpty({1, 2}) = {{1, 2}, {1}, {2}}

Null(S) == S \union {nil}

Max(S) == CHOOSE x \in S: \A y \in S: y <= x

ASSUME Max({11, 12, 13}) = 13

Min(S) == CHOOSE x \in S: \A y \in S: y >= x

ASSUME Min({11, 12, 13}) = 11

Range(f) == {f[x]: x \in DOMAIN f}

--------------------------------------------------------------

Epoch == 10..19

LogPos == 0..max_num_action

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

----------------------

IsPosMap(m) ==
    /\ DOMAIN m \subseteq Node
    /\ \A x \in DOMAIN m: m[x] \in LogPos

LeaderPosMapTypeOK ==
    /\ DOMAIN leader_pos_map = Node
    /\ \A n \in Node:
        leader_pos_map[n] # nil => IsPosMap(leader_pos_map[n])

--------------------------------------------------------------

TypeOK ==
    /\ global_config \in Config

    /\ local_config \in [Node -> Null(Config)]
    /\ local_epoch \in [Node -> Null(Epoch)]
    /\ log \in [Node -> Seq(LogEntry)]
    /\ commit_pos \in [Node -> LogPos]

    /\ num_action \in 0..max_num_action

    /\ msgs \subseteq Msg

Init ==
    /\ \E nodes \in NonEmpty(Node): \E l \in nodes:
        /\ global_config = init_config(nodes, l)

    /\ local_config = [n \in Node |-> nil]
    /\ local_epoch = [n \in Node |-> nil]
    /\ log = [n \in Node |-> <<>>]
    /\ leader_pos_map = [n \in Node |-> nil]
    /\ commit_pos = [n \in Node |-> 0]

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

isLocalLeader(n) ==
    /\ local_config[n] # nil
    /\ local_config[n].leader = n

isLeader(n) ==
    /\ isLocalLeader(n)
    /\ local_config[n].epoch = global_config.epoch

allowAction ==
    /\ num_action < max_num_action
    /\ num_action' = num_action + 1

--------------------------------------------------------------

SyncConfig(n) ==
    LET
        epoch == global_config.epoch
        isr == global_config.isr
        pos_map_domain == isr \ {n}

        init_pos_map == [x \in pos_map_domain |-> 0]
    IN
    /\ local_config[n] # nil => local_config[n].epoch < epoch
    /\ local_config' = [local_config EXCEPT ![n] = global_config]
    /\ updateEpoch(n, epoch)

    /\ IF global_config.leader = n
        THEN leader_pos_map' = [leader_pos_map EXCEPT ![n] = init_pos_map]
        ELSE UNCHANGED leader_pos_map

    /\ UNCHANGED num_action
    /\ UNCHANGED commit_pos
    /\ UNCHANGED log
    /\ UNCHANGED global_config
    /\ UNCHANGED msgs

--------------------------------------------------------------

updateCommitPos(n) ==
    LET
        leader_pos == Len(log'[n])
        repl_pos_list == Range(leader_pos_map'[n])
        new_pos == Min({leader_pos} \union repl_pos_list)
    IN
    /\ commit_pos' = [commit_pos EXCEPT ![n] = new_pos]

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
    /\ UNCHANGED leader_pos_map
    /\ updateCommitPos(n)

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

    /\ UNCHANGED leader_pos_map
    /\ UNCHANGED commit_pos
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
    LET
        leader == global_config.leader
        isr == global_config.isr
    IN
    /\ num_action = max_num_action
    /\ Len(log[leader]) = commit_pos[leader]
    /\ \A n \in isr:
        /\ local_config[n] # nil
        /\ local_config[n].epoch = global_config.epoch
        /\ commit_pos[n] = commit_pos[leader]

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

LeaderInv ==
    \A n \in Node:
        isLocalLeader(n) <=> leader_pos_map[n] # nil

----------------------

computed_commit_pos(n) ==
    LET
        leader_pos == Len(log[n])
        repl_pos_list == Range(leader_pos_map[n])
    IN
    Min({leader_pos} \union repl_pos_list)

CommitPosInv ==
    \A n \in Node:
        isLocalLeader(n) =>
            commit_pos[n] = computed_commit_pos(n)

====

---- MODULE DBReplV2 ----
EXTENDS TLC, Naturals, Sequences, FiniteSets

CONSTANTS Node, Value, max_num_action, nil

VARIABLES
    global_config,
    local_config, local_epoch,
    log, god_log,
    commit_pos, retention_pos,
    leader_pos_map, leader_syncing,
    leader_need_add, valid_log_pos,
    num_action

vars == <<
    global_config,
    local_config, local_epoch,
    log, god_log,
    commit_pos, retention_pos,
    leader_pos_map, leader_syncing,
    leader_need_add, valid_log_pos,
    num_action
>>

----------------------------------------------------------------------

NonEmpty(S) == (SUBSET S) \ {{}}

ASSUME NonEmpty({11, 12}) = {{11}, {12}, {11, 12}}

Null(S) == S \union {nil}

Min(S) == CHOOSE x \in S: \A y \in S: x <= y

ASSUME Min({11, 12, 13}) = 11

----------------------------------------------------------------------

Epoch == 10..(10 + max_num_action)

Revision == 20..29

LogPos == 0..max_num_action

--------------------

Config == [
    epoch: Epoch,
    isr: NonEmpty(Node),
    adding: SUBSET Node,
    leader: Node,
    revision: Revision
]

init_config(nodes, l) == [
    epoch |-> 11,
    isr |-> nodes,
    adding |-> {},
    leader |-> l,
    revision |-> 20
]

--------------------

LogEntry == [
    pos: LogPos,
    epoch: Epoch,
    value: Value
]

----------------------------------------------------------------------

TypeOK ==
    /\ global_config \in Config

    /\ local_config \in [Node -> Null(Config)]
    /\ local_epoch \in [Node -> Epoch]

    /\ log \in [Node -> Seq(LogEntry)]
    /\ god_log \in Seq(LogEntry)

    /\ commit_pos \in [Node -> LogPos]
    /\ retention_pos \in [Node -> LogPos]

    /\ leader_syncing \in [Node -> SUBSET Node]
    /\ leader_need_add \in [Node -> SUBSET Node]

    /\ valid_log_pos \in [Node -> LogPos]

    /\ num_action \in 0..max_num_action

Init ==
    /\ \E nodes \in NonEmpty(Node): \E l \in nodes:
            global_config = init_config(nodes, l)

    /\ local_config = [n \in Node |-> nil]
    /\ local_epoch = [n \in Node |-> 10]

    /\ log = [n \in Node |-> <<>>]
    /\ god_log = <<>>

    /\ commit_pos = [n \in Node |-> 0]
    /\ retention_pos = [n \in Node |-> 0]

    /\ leader_pos_map = [n \in Node |-> nil]
    /\ leader_syncing = [n \in Node |-> {}]
    /\ leader_need_add = [n \in Node |-> {}]

    /\ valid_log_pos = [n \in Node |-> 0]

    /\ num_action = 0

----------------------------------------------------------------------

isLocalLeader(n) ==
    /\ local_config[n] # nil
    /\ local_config[n].epoch = local_epoch[n]
    /\ n = local_config[n].leader

--------------------

computePosMapDomain(n, conf) ==
    conf.adding \union (conf.isr \ {n})

--------------------

updateLocalEpoch(n, new_epoch) ==
    IF new_epoch > local_epoch[n] THEN
        local_epoch' = [local_epoch EXCEPT ![n] = new_epoch]
    ELSE
        UNCHANGED local_epoch

--------------------

updateCommitPos(n, isr) ==
    LET
        self_pos == Len(log'[n])
        pos_map == leader_pos_map'[n]
        check_set == isr \ {n}

        pos_list == {pos_map[x]: x \in check_set}
        new_pos == Min({self_pos} \union pos_list)

        new_god_entries ==
            IF new_pos > Len(god_log) THEN
                SubSeq(log'[n], Len(god_log) + 1, new_pos)
            ELSE
                <<>>
    IN
    /\ commit_pos' = [commit_pos EXCEPT ![n] = new_pos]
    /\ god_log' = god_log \o new_god_entries

--------------------

updateLeaderNeedAdd(n, conf) ==
    /\ UNCHANGED leader_need_add \* TODO

--------------------

allowAction ==
    /\ num_action < max_num_action
    /\ num_action' = num_action + 1

--------------------

getEffectiveISR(n) ==
    local_config[n].isr \* TODO

--------------------

getFollowerSet(n) ==
    local_config[n].isr \union local_config[n].adding

--------------------

isFollowerOf(l, x) ==
    /\ isLocalLeader(l)
    /\ local_epoch[l] = local_epoch[x]
    /\ x \in getFollowerSet(l)
    /\ x # l

----------------------------------------------------------------------

initLeaderPosMap(n, conf) ==
    LET
        new_domain == computePosMapDomain(n, conf)

        init_fn(x) ==
            IF x \in conf.isr
                THEN commit_pos[n]
                ELSE retention_pos[n]
    IN
        [x \in new_domain |-> init_fn(x)]

SyncConfig(n) ==
    LET
        conf == global_config

        is_config_leader ==
            /\ conf.epoch = local_epoch'[n]
            /\ n = conf.leader

        epoch_changed ==
            local_config[n] # nil => local_config[n].epoch < conf.epoch

        init_pos_map == initLeaderPosMap(n, conf)

        on_leader_epoch_changed ==
            /\ leader_pos_map' = [leader_pos_map EXCEPT ![n] = init_pos_map]
            /\ leader_syncing' = [leader_syncing EXCEPT ![n] = conf.isr \ {n}]

        on_leader_epoch_same ==
            /\ UNCHANGED leader_syncing \* TODO

        on_leader ==
            /\ IF epoch_changed
                THEN on_leader_epoch_changed
                ELSE on_leader_epoch_same
            /\ updateCommitPos(n, conf.isr)
            /\ updateLeaderNeedAdd(n, conf)

        on_follower ==
            /\ leader_pos_map' = [leader_pos_map EXCEPT ![n] = nil]
            /\ leader_syncing' = [leader_syncing EXCEPT ![n] = {}]
            /\ leader_need_add' = [leader_need_add EXCEPT ![n] = {}]
            /\ UNCHANGED commit_pos
            /\ UNCHANGED god_log
    IN
    /\ local_config[n] # nil => local_config[n].revision < conf.revision

    /\ local_config' = [local_config EXCEPT ![n] = conf]
    /\ updateLocalEpoch(n, conf.epoch)

    /\ UNCHANGED log

    /\ IF is_config_leader
        THEN on_leader
        ELSE on_follower

    /\ UNCHANGED valid_log_pos
    /\ UNCHANGED retention_pos
    /\ UNCHANGED num_action
    /\ UNCHANGED global_config

----------------------------------------------------------------------

AddLogEntry(n, v) ==
    LET
        pos == Len(log[n]) + 1

        entry == [
            pos |-> pos,
            epoch |-> local_epoch[n],
            value |-> v
        ]
    IN
    /\ isLocalLeader(n)
    /\ local_epoch[n] = global_config.epoch
    /\ allowAction

    /\ log' = [log EXCEPT ![n] = Append(@, entry)]
    /\ valid_log_pos' = [valid_log_pos EXCEPT ![n] = pos]
    /\ UNCHANGED leader_pos_map
    /\ updateCommitPos(n, getEffectiveISR(n))

    /\ UNCHANGED leader_need_add
    /\ UNCHANGED leader_syncing

    /\ UNCHANGED retention_pos
    /\ UNCHANGED local_epoch
    /\ UNCHANGED local_config
    /\ UNCHANGED global_config

----------------------------------------------------------------------

TerminateCond ==
    LET
        leader == global_config.leader
        isr == global_config.isr
    IN
    /\ num_action = max_num_action
    /\ global_config.adding = {}
    /\ Len(log[leader]) = commit_pos[leader]
    /\ leader_need_add[leader] = {}
    /\ leader_syncing[leader] = {}
    /\ \A n \in isr:
        /\ local_config[n] # nil
        /\ local_config[n] = global_config
        /\ local_epoch[n] = global_config.epoch
        /\ commit_pos[n] = commit_pos[leader]

Terminated ==
    /\ TerminateCond
    /\ UNCHANGED vars

----------------------------------------------------------------------

Next ==
    \/ \E n \in Node:
        \/ SyncConfig(n)
    \/ \E n \in Node, v \in Value:
        \/ AddLogEntry(n, v)
    \/ Terminated

Spec == Init /\ [][Next]_vars

----------------------------------------------------------------------

isValidConfig(conf) ==
    /\ conf.leader \in conf.isr
    /\ conf.isr \intersect conf.adding = {}

ConfigInv ==
    /\ isValidConfig(global_config)
    /\ \A n \in Node:
        local_config[n] # nil => isValidConfig(local_config[n])

--------------------

LeaderPosMapInv ==
    \A n \in Node:
        isLocalLeader(n) <=> leader_pos_map[n] # nil

--------------------

LeaderPosMapDomainInv ==
    \A n \in Node:
        LET
            conf == local_config[n]
            expected == computePosMapDomain(n, conf)
        IN
        isLocalLeader(n) =>
            DOMAIN leader_pos_map[n] = expected

--------------------

LeaderCommitPosInv ==
    \A n \in Node:
        LET
            self_pos == Len(log[n])

            pos_map == leader_pos_map[n]

            check_set == getEffectiveISR(n) \ {n}

            pos_list == {pos_map[x]: x \in check_set}

            expected == Min({self_pos} \union pos_list)
        IN
        /\ isLocalLeader(n) => commit_pos[n] = expected

--------------------

NodeLogPosInv ==
    \A n \in Node:
        /\ commit_pos[n] <= Len(log[n])
        /\ valid_log_pos[n] <= Len(log[n])
        /\ valid_log_pos[n] >= commit_pos[n]
        /\ retention_pos[n] <= commit_pos[n]

--------------------

FollowerInv ==
    \A n \in Node:
        ~isLocalLeader(n) =>
            /\ leader_need_add[n] = {}
            /\ leader_syncing[n] = {}

--------------------

LeaderInv ==
    \A n \in Node:
        isLocalLeader(n) =>
            /\ leader_need_add[n] \subseteq local_config[n].adding
            /\ leader_syncing[n] \subseteq local_config[n].isr
            /\ valid_log_pos[n] = Len(log[n])

--------------------

LocalEpochInv ==
    \A n \in Node:
        local_config[n] # nil => local_config[n].epoch <= local_epoch[n]

--------------------

GodLogMatchISR ==
    \A n \in Node:
        n \in global_config.isr =>
            /\ Len(god_log) <= Len(log[n])
            /\ god_log = SubSeq(log[n], 1, Len(god_log))

--------------------

GodLogLenMatchCommitPos ==
    \A n \in Node:
        isLocalLeader(n) =>
            commit_pos[n] <= Len(god_log)

--------------------

LogPosInv ==
    \A n \in Node:
        \A pos \in DOMAIN log[n]:
            log[n][pos].pos = pos

--------------------

FollowerValidLogMatching ==
    \A l \in Node, x \in Node:
        LET
            end_pos == valid_log_pos[x]

            leader_log == SubSeq(log[l], 1, end_pos)
            follower_log == SubSeq(log[x], 1, end_pos)
        IN
        isFollowerOf(l, x) =>
            /\ valid_log_pos[x] <= Len(log[l])
            /\ leader_log = follower_log

====

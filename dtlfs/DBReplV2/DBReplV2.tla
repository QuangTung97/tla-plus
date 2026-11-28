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

Epoch == 10..(11 + max_num_action)

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

updateLeaderNeedAdd(l, conf) ==
    LET
        pos_map == leader_pos_map'[l]

        allow_move(x) ==
            /\ leader_syncing'[l] = {}
            /\ pos_map[x] >= commit_pos'[l]

        move_set == {x \in conf.adding: allow_move(x)}
    IN
    /\ leader_need_add' = [leader_need_add EXCEPT ![l] = move_set]

--------------------

allowAction ==
    /\ num_action < max_num_action
    /\ num_action' = num_action + 1

--------------------

getEffectiveISR(n) ==
    local_config[n].isr \union leader_need_add[n]

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

----------------------------------------------------------------------

updateLeaderPosMap(n, conf) ==
    LET
        new_domain == computePosMapDomain(n, conf)

        pos_map == leader_pos_map[n]
        old_domain == DOMAIN pos_map

        update_fn(x) ==
            IF x \in old_domain THEN
                pos_map[x]
            ELSE
                retention_pos[n]

        new_map == [x \in new_domain |-> update_fn(x)]
    IN
    /\ leader_pos_map' = [leader_pos_map EXCEPT ![n] = new_map]

----------------------------------------------------------------------

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
            /\ updateLeaderPosMap(n, conf)
            /\ leader_syncing' = [leader_syncing EXCEPT
                    ![n] = @ \intersect conf.isr
                ]

        on_leader ==
            /\ IF epoch_changed
                THEN on_leader_epoch_changed
                ELSE on_leader_epoch_same
            /\ updateCommitPos(n, conf.isr)
            /\ updateLeaderNeedAdd(n, conf)
            /\ valid_log_pos' = [valid_log_pos EXCEPT ![n] = Len(log[n])]

        on_follower_epoch_changed ==
            /\ valid_log_pos' = [valid_log_pos EXCEPT ![n] = commit_pos[n]]

        on_follower_epoch_same ==
            /\ UNCHANGED valid_log_pos

        on_follower ==
            /\ leader_pos_map' = [leader_pos_map EXCEPT ![n] = nil]
            /\ leader_syncing' = [leader_syncing EXCEPT ![n] = {}]
            /\ leader_need_add' = [leader_need_add EXCEPT ![n] = {}]
            /\ IF epoch_changed
                THEN on_follower_epoch_changed
                ELSE on_follower_epoch_same
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

configUnchanged ==
    /\ UNCHANGED num_action
    /\ UNCHANGED retention_pos
    /\ UNCHANGED local_epoch
    /\ UNCHANGED local_config
    /\ UNCHANGED global_config

SyncLogEntry(l, x) ==
    LET
        pos_map == leader_pos_map[l]
        pos == pos_map[x] + 1

        entry == log[l][pos]

        on_append ==
            /\ log' = [log EXCEPT ![x] = Append(@, entry)]

        on_update ==
            /\ log' = [log EXCEPT ![x][pos] = entry]
    IN
    /\ isFollowerOf(l, x)
    /\ pos <= Len(log[l])
    /\ pos > valid_log_pos[x]

    /\ valid_log_pos' = [valid_log_pos EXCEPT ![x] = pos]
    /\ IF pos > Len(log[x])
        THEN on_append
        ELSE on_update

    /\ UNCHANGED commit_pos
    /\ UNCHANGED god_log

    /\ UNCHANGED leader_pos_map
    /\ UNCHANGED leader_syncing
    /\ UNCHANGED leader_need_add

    /\ configUnchanged

----------------------------------------------------------------------

UpdateLeaderPosMap(l, x) ==
    LET
        pos == valid_log_pos[x]
        pos_map == leader_pos_map[l]

        allow_cond ==
            \/ pos > pos_map[x]
            \/ /\ pos = pos_map[x]
               /\ x \in leader_syncing[l]

        is_last_entry == pos = Len(log[x])

        clear_syncing ==
            leader_syncing' = [leader_syncing EXCEPT ![l] = @ \ {x}]
    IN
    /\ isFollowerOf(l, x)
    /\ allow_cond

    /\ leader_pos_map' = [leader_pos_map EXCEPT ![l][x] = pos]
    /\ UNCHANGED log
    /\ updateCommitPos(l, getEffectiveISR(l))
    /\ IF is_last_entry
        THEN clear_syncing
        ELSE UNCHANGED leader_syncing
    /\ updateLeaderNeedAdd(l, local_config[l])

    /\ UNCHANGED valid_log_pos
    /\ configUnchanged

----------------------------------------------------------------------

FollowerSyncCommitPos(l, x) ==
    LET
        pos == commit_pos[l]
    IN
    /\ isFollowerOf(l, x)
    /\ pos > commit_pos[x]
    /\ pos <= Len(log[x])

    /\ commit_pos' = [commit_pos EXCEPT ![x] = pos]

    /\ UNCHANGED log
    /\ UNCHANGED god_log
    /\ UNCHANGED valid_log_pos
    /\ UNCHANGED leader_pos_map
    /\ UNCHANGED leader_syncing
    /\ UNCHANGED leader_need_add
    /\ configUnchanged

----------------------------------------------------------------------

UpdateGlobalConfig(nodes) ==
    LET
        old_nodes == global_config.isr \union global_config.adding

        old_isr == global_config.isr
        new_isr == old_isr \intersect nodes

        new_adding == nodes \ new_isr

        leader_unchanged ==
            global_config.leader \in new_isr

        update_member_only ==
            global_config' = [global_config EXCEPT
                !.isr = new_isr,
                !.adding = new_adding,
                !.revision = @ + 1
            ]

        update_leader(l) ==
            global_config' = [
                epoch |-> global_config.epoch + 1,
                isr |-> new_isr,
                adding |-> new_adding,
                leader |-> l,
                revision |-> global_config.revision + 1
            ]
    IN
    /\ allowAction
    /\ nodes # old_nodes
    /\ new_isr # {}

    /\ IF leader_unchanged
        THEN update_member_only
        ELSE \E l \in new_isr: update_leader(l)

    /\ UNCHANGED commit_pos
    /\ UNCHANGED retention_pos
    /\ UNCHANGED log
    /\ UNCHANGED god_log

    /\ UNCHANGED local_config
    /\ UNCHANGED local_epoch
    /\ UNCHANGED leader_pos_map
    /\ UNCHANGED leader_syncing
    /\ UNCHANGED leader_need_add
    /\ UNCHANGED valid_log_pos

----------------------------------------------------------------------

AddToGlobalISR(l, x) ==
    /\ isLocalLeader(l)
    /\ local_config[l].revision = global_config.revision
    /\ x \in leader_need_add[l]

    /\ leader_need_add' = [leader_need_add EXCEPT ![l] = @ \ {x}]
    /\ local_config' = [local_config EXCEPT
            ![l].adding = @ \ {x},
            ![l].isr = @ \union {x}
        ]
    /\ global_config' = [global_config EXCEPT
            !.adding = @ \ {x},
            !.isr = @ \union {x},
            !.revision = @ + 1
        ]

    /\ UNCHANGED log
    /\ UNCHANGED god_log
    /\ UNCHANGED local_epoch
    /\ UNCHANGED commit_pos
    /\ UNCHANGED num_action
    /\ UNCHANGED valid_log_pos
    /\ UNCHANGED retention_pos
    /\ UNCHANGED leader_pos_map
    /\ UNCHANGED leader_syncing

\* TODO sync follower epoch

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
    \/ \E l \in Node, x \in Node:
        \/ SyncLogEntry(l, x)
        \/ UpdateLeaderPosMap(l, x)
        \/ FollowerSyncCommitPos(l, x)
        \/ AddToGlobalISR(l, x)
    \/ \E nodes \in NonEmpty(Node):
        \/ UpdateGlobalConfig(nodes)
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

--------------------

LeaderNeedAddAndSyncingNodes ==
    \A n \in Node:
        leader_need_add[n] # {} => leader_syncing[n] = {}

--------------------

LeaderNeedAddSetMatchLeaderPos ==
    \A n \in Node:
        LET
            pre_cond ==
                /\ isLocalLeader(n)
                /\ leader_syncing[n] = {}

            pos_map == leader_pos_map[n]

            adding_set ==
                local_config[n].adding \ leader_need_add[n]

            cond ==
                \A x \in adding_set:
                    /\ pos_map[x] < commit_pos[n]
        IN
            pre_cond => cond

====

---- MODULE DBReplication ----
EXTENDS TLC, Naturals, Sequences, FiniteSets

CONSTANTS Node, Value, nil, max_num_action

VARIABLES
    global_config,
    local_config, log, god_log,
    leader_pos_map, commit_pos,
    follower_ready, leader_syncing_nodes, local_need_add,
    num_action

vars == <<
    global_config,
    local_config, log, god_log,
    leader_pos_map, commit_pos,
    follower_ready, leader_syncing_nodes, local_need_add,
    num_action
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

Epoch == 10..(10 + max_num_action)

Revision == 20..29

LogPos == 0..max_num_action

----------------------

Config == [
    epoch: Epoch,
    isr: NonEmpty(Node),
    adding: SUBSET Node,
    leader: Node,
    revision: Revision
]

init_config(nodes, l) == [
    epoch |-> 10,
    isr |-> nodes,
    adding |-> {},
    leader |-> l,
    revision |-> 20
]

----------------------

LogEntry == [
    epoch: Epoch,
    pos: LogPos,
    value: Value
]

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

    /\ log \in [Node -> Seq(LogEntry)]
    /\ god_log \in Seq(LogEntry)
    /\ commit_pos \in [Node -> LogPos]
    /\ follower_ready \in [Node -> Null(BOOLEAN)]
    /\ leader_syncing_nodes \in [Node -> SUBSET Node]
    /\ local_need_add \in [Node -> SUBSET Node]

    /\ num_action \in 0..max_num_action

Init ==
    /\ \E nodes \in NonEmpty(Node): \E l \in nodes:
        /\ global_config = init_config(nodes, l)

    /\ local_config = [n \in Node |-> nil]

    /\ log = [n \in Node |-> <<>>]
    /\ god_log = <<>>
    /\ leader_pos_map = [n \in Node |-> nil]
    /\ commit_pos = [n \in Node |-> 0]
    /\ follower_ready = [n \in Node |-> nil]
    /\ leader_syncing_nodes = [n \in Node |-> {}]
    /\ local_need_add = [n \in Node |-> {}]

    /\ num_action = 0

--------------------------------------------------------------

isLocalLeader(n) ==
    /\ local_config[n] # nil
    /\ local_config[n].leader = n

isLeader(n) ==
    /\ isLocalLeader(n)
    /\ local_config[n].epoch = global_config.epoch

isLocalFollower(n) ==
    /\ local_config[n] # nil
    /\ local_config[n].leader # n

-------------------

allowAction ==
    /\ num_action < max_num_action
    /\ num_action' = num_action + 1

-------------------

computePosMapDomain(n, isr, adding) ==
    adding \union (isr \ {n})

--------------------------------------------------------------

updateCommitPos(n, isr) ==
    LET
        leader_pos == Len(log'[n])
        check_set == isr \ {n}
        repl_pos_list == {leader_pos_map'[n][x]: x \in check_set}
        new_pos == Min({leader_pos} \union repl_pos_list)

        new_god_entries ==
            IF new_pos > Len(god_log) THEN
                SubSeq(log'[n], Len(god_log) + 1, new_pos)
            ELSE
                <<>>
    IN
    /\ commit_pos' = [commit_pos EXCEPT ![n] = new_pos]
    /\ god_log' = god_log \o new_god_entries

-------------------

initLeaderPosMap(n, isr, adding, init_val) ==
    LET
        new_domain == computePosMapDomain(n, isr, adding)

        init_fn(x) ==
            IF x \in isr
                THEN init_val
                ELSE 0

        init_pos_map == [x \in new_domain |-> init_fn(x)]
    IN
    /\ leader_pos_map' = [leader_pos_map EXCEPT ![n] = init_pos_map]

-------------------

updateLeaderPosMap(n, isr, adding) ==
    LET
        new_domain == computePosMapDomain(n, isr, adding)
        old_domain == DOMAIN leader_pos_map[n]

        update_fn(x, old) ==
            IF x \in old_domain
                THEN old
                ELSE 0

        do_update(old_map) ==
            [x \in new_domain |-> update_fn(x, old_map[x])]
    IN
    /\ leader_pos_map' = [leader_pos_map EXCEPT ![n] = do_update(@)]

--------------------------------------------------------------

moveAddingToLocalNeedAdd(n, conf) ==
    LET
        pos_map == leader_pos_map'[n]

        allow_move(x) ==
            /\ leader_syncing_nodes'[n] = {}
            /\ pos_map[x] >= commit_pos'[n]

        move_set == {x \in conf.adding: allow_move(x)}
    IN
    /\ local_need_add' = [local_need_add EXCEPT ![n] = move_set]

--------------------------------------------------------------

SyncConfig(n) ==
    LET
        conf == global_config
        revision == conf.revision

        epoch == conf.epoch
        epoch_changed ==
            local_config[n] # nil =>
                local_config[n].epoch < conf.epoch

        isr == conf.isr

        on_leader_epoch_changed ==
            /\ initLeaderPosMap(n, isr, conf.adding, commit_pos[n])
            /\ follower_ready' = [follower_ready EXCEPT ![n] = nil]
            /\ leader_syncing_nodes' = [leader_syncing_nodes EXCEPT
                    ![n] = conf.isr \ {n}
                ]

        on_leader_epoch_not_changed ==
            /\ updateLeaderPosMap(n, isr, conf.adding)
            /\ leader_syncing_nodes' = [leader_syncing_nodes EXCEPT
                    ![n] = @ \intersect conf.isr
                ]
            /\ UNCHANGED follower_ready

        on_leader ==
            /\ IF epoch_changed
                THEN on_leader_epoch_changed
                ELSE on_leader_epoch_not_changed
            /\ updateCommitPos(n, isr)
            /\ moveAddingToLocalNeedAdd(n, conf)

        on_follower_epoch_changed ==
            /\ leader_pos_map' = [leader_pos_map EXCEPT ![n] = nil]
            /\ follower_ready' = [follower_ready EXCEPT ![n] = FALSE]
            /\ local_need_add' = [local_need_add EXCEPT ![n] = {}]
            /\ leader_syncing_nodes' = [leader_syncing_nodes EXCEPT ![n] = {}]
            /\ UNCHANGED commit_pos

        on_follower_epoch_not_changed ==
            /\ UNCHANGED leader_pos_map
            /\ UNCHANGED follower_ready
            /\ UNCHANGED local_need_add
            /\ UNCHANGED leader_syncing_nodes

        on_follower ==
            /\ IF epoch_changed
                THEN on_follower_epoch_changed
                ELSE on_follower_epoch_not_changed
            /\ UNCHANGED commit_pos
            /\ UNCHANGED god_log
    IN
    /\ local_config[n] # nil => local_config[n].revision < revision

    /\ local_config' = [local_config EXCEPT ![n] = conf]
    /\ UNCHANGED log
    /\ IF conf.leader = n
        THEN on_leader
        ELSE on_follower

    /\ UNCHANGED num_action
    /\ UNCHANGED global_config

--------------------------------------------------------------

getEffectiveISR(n) ==
    local_config[n].isr \union local_need_add[n]

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
    IN
    /\ isLeader(n)
    /\ allowAction

    /\ log' = [log EXCEPT ![n] = Append(@, entry)]
    /\ UNCHANGED leader_pos_map
    /\ updateCommitPos(n, getEffectiveISR(n))

    /\ UNCHANGED leader_syncing_nodes
    /\ UNCHANGED local_need_add
    /\ UNCHANGED follower_ready
    /\ UNCHANGED local_config
    /\ UNCHANGED global_config

--------------------------------------------------------------

getFollowerSetOf(l) ==
    local_config[l].isr \union local_config[l].adding

--------------------------------------------------------------

isFollowerOf(l, x) ==
    /\ isLocalLeader(l)
    /\ x \in getFollowerSetOf(l)
    /\ x # l
    /\ local_config[x] # nil
    /\ local_config[x].epoch = local_config[l].epoch

--------------------------------------------------------------

configUnchanged ==
    /\ UNCHANGED local_config
    /\ UNCHANGED num_action
    /\ UNCHANGED global_config

--------------------------------------------------------------

getLogEntry(n, pos) ==
    IF pos > Len(log[n])
        THEN nil
        ELSE log[n][pos]

--------------------------------------------------------------

RECURSIVE firstNonEqualLogEntry(_, _, _)

firstNonEqualLogEntry(l, n, pos) ==
    LET
        entry1 == getLogEntry(l, pos)
        entry2 == getLogEntry(n, pos)
    IN
        IF entry1 = nil \/ entry2 = nil THEN
            pos
        ELSE IF entry1.epoch = entry2.epoch THEN
            firstNonEqualLogEntry(l, n, pos + 1)
        ELSE
            pos

--------------------------------------------------------------

TruncateFollowerLog(l, n) ==
    LET
        match_pos == firstNonEqualLogEntry(l, n, 1) - 1
    IN
    /\ isFollowerOf(l, n)
    /\ ~follower_ready[n]

    /\ follower_ready' = [follower_ready EXCEPT ![n] = TRUE]
    /\ log' = [log EXCEPT ![n] = SubSeq(@, 1, match_pos)]

    /\ UNCHANGED leader_syncing_nodes
    /\ UNCHANGED local_need_add
    /\ UNCHANGED commit_pos
    /\ UNCHANGED god_log
    /\ UNCHANGED leader_pos_map
    /\ configUnchanged

--------------------------------------------------------------

recvAcceptEntry(n, entry) ==
    LET
        pos == entry.pos
        highest_pos == Len(log[n])
    IN
    /\ pos = highest_pos + 1

RecvEntry(l, n) ==
    LET
        handle_entry(entry) ==
            /\ recvAcceptEntry(n, entry)
            /\ log' = [log EXCEPT ![n] = Append(@, entry)]
    IN
    /\ isFollowerOf(l, n)
    /\ follower_ready[n]

    /\ \E entry \in Range(log[l]):
        \/ handle_entry(entry)

    /\ UNCHANGED leader_pos_map
    /\ UNCHANGED leader_syncing_nodes
    /\ UNCHANGED follower_ready
    /\ UNCHANGED commit_pos
    /\ UNCHANGED god_log
    /\ UNCHANGED local_need_add
    /\ configUnchanged

--------------------------------------------------------------

IncLeaderLogPos(l, x) ==
    LET
        pos == Len(log[x])

        allow_cond ==
            \/ leader_pos_map[l][x] < pos
            \/ /\ leader_pos_map[l][x] = pos
               /\ x \in leader_syncing_nodes[l]
    IN
    /\ isFollowerOf(l, x)
    /\ follower_ready[x]
    /\ allow_cond

    /\ leader_pos_map' = [leader_pos_map EXCEPT ![l][x] = pos]
    /\ leader_syncing_nodes' = [leader_syncing_nodes EXCEPT ![l] = @ \ {x}]
    /\ UNCHANGED log
    /\ updateCommitPos(l, getEffectiveISR(l))
    /\ moveAddingToLocalNeedAdd(l, local_config[l])

    /\ UNCHANGED local_config
    /\ UNCHANGED follower_ready
    /\ UNCHANGED num_action
    /\ UNCHANGED global_config

--------------------------------------------------------------

IncFollowerCommitPos(l, n) ==
    LET
        pos == commit_pos[l]
    IN
    /\ isFollowerOf(l, n)
    /\ follower_ready[n]
    /\ commit_pos[n] < pos
    /\ Len(log[n]) >= pos

    /\ commit_pos' = [commit_pos EXCEPT ![n] = pos]

    /\ UNCHANGED local_need_add
    /\ UNCHANGED follower_ready
    /\ UNCHANGED leader_pos_map
    /\ UNCHANGED leader_syncing_nodes
    /\ UNCHANGED log
    /\ UNCHANGED god_log
    /\ configUnchanged

--------------------------------------------------------------

UpdateGlobalConfig(new_nodes) ==
    LET
        isr == global_config.isr
        old_nodes == global_config.isr \union global_config.adding

        new_isr == isr \intersect new_nodes

        new_epoch(l) ==
            IF l = global_config.leader
                THEN global_config.epoch
                ELSE global_config.epoch + 1 \* inc when leader change

        new_config(l) == [
            epoch |-> new_epoch(l),
            isr |-> new_isr,
            adding |-> new_nodes \ isr,
            leader |-> l,
            revision |-> global_config.revision + 1
        ]
    IN
    /\ allowAction
    /\ old_nodes # new_nodes
    /\ new_isr # {}

    /\ \E l \in new_isr:
        /\ global_config' = new_config(l)

    /\ UNCHANGED local_config
    /\ UNCHANGED commit_pos
    /\ UNCHANGED leader_pos_map
    /\ UNCHANGED follower_ready
    /\ UNCHANGED leader_syncing_nodes
    /\ UNCHANGED local_need_add
    /\ UNCHANGED <<log, god_log>>

--------------------------------------------------------------

AddToGlobalISR(n, x) ==
    /\ isLocalLeader(n)
    /\ x \in local_need_add[n]
    /\ local_config[n].revision = global_config.revision

    /\ local_need_add' = [local_need_add EXCEPT ![n] = @ \ {x}]
    /\ global_config' = [global_config EXCEPT
            !.adding = @ \ {x},
            !.isr = @ \union {x},
            !.revision = @ + 1
        ]
    /\ local_config' = [local_config EXCEPT
            ![n].adding = @ \ {x},
            ![n].isr = @ \union {x}
        ]

    /\ UNCHANGED follower_ready
    /\ UNCHANGED leader_pos_map
    /\ UNCHANGED leader_syncing_nodes
    /\ UNCHANGED num_action
    /\ UNCHANGED <<log, god_log>>
    /\ UNCHANGED commit_pos

--------------------------------------------------------------

TerminateCond ==
    LET
        leader == global_config.leader
        isr == global_config.isr
    IN
    /\ num_action = max_num_action
    /\ global_config.adding = {}
    /\ Len(log[leader]) = commit_pos[leader]
    /\ \A n \in isr:
        /\ local_config[n] # nil
        /\ local_config[n] = global_config
        /\ commit_pos[n] = commit_pos[leader]
        /\ local_need_add[n] = {}
        /\ leader_syncing_nodes[n] = {}

Terminated ==
    /\ TerminateCond
    /\ UNCHANGED vars

--------------------------------------------------------------

Next ==
    \/ \E n \in Node:
        \/ SyncConfig(n)
    \/ \E n \in Node, v \in Value:
        \/ AddEntry(n, v)
    \/ \E l \in Node, n \in Node:
        \/ TruncateFollowerLog(l, n)
        \/ RecvEntry(l, n)
        \/ IncLeaderLogPos(l, n)
        \/ IncFollowerCommitPos(l, n)
        \/ AddToGlobalISR(l, n)
    \/ \E nodes \in NonEmpty(Node):
        \/ UpdateGlobalConfig(nodes)
    \/ Terminated

Spec == Init /\ [][Next]_vars

--------------------------------------------------------------

GlobalConfigInv ==
    /\ global_config.isr \intersect global_config.adding = {}
    /\ global_config.leader \in global_config.isr

----------------------

LeaderInv ==
    \A n \in Node:
        /\ isLocalLeader(n) <=> leader_pos_map[n] # nil
        /\ isLocalLeader(n) => follower_ready[n] = nil

----------------------

FollowerInv ==
    \A n \in Node:
        isLocalFollower(n) =>
            /\ follower_ready[n] \in BOOLEAN
            /\ leader_syncing_nodes[n] = {}
            /\ local_need_add[n] = {}

----------------------

LogPosInv ==
    \A n \in Node: \A pos \in DOMAIN log[n]:
        log[n][pos].pos = pos

----------------------

LeaderPosMapInv ==
    \A n \in Node:
        LET
            expected == computePosMapDomain(
                n,
                local_config[n].isr,
                local_config[n].adding
            )
        IN
        isLocalLeader(n) =>
            DOMAIN leader_pos_map[n] = expected

----------------------

CommitPosInv ==
    \A n \in Node:
        commit_pos[n] <= Len(log[n])

----------------------

computed_commit_pos(n) ==
    LET
        leader_pos == Len(log[n])
        isr == getEffectiveISR(n) \ {n}
        repl_pos_list == {leader_pos_map[n][x]: x \in isr}
    IN
    Min({leader_pos} \union repl_pos_list)

LeaderCommitPosInv ==
    \A n \in Node:
        isLocalLeader(n) =>
            commit_pos[n] = computed_commit_pos(n)

----------------------

commitPosNeverDecStep ==
    \A n \in Node: commit_pos[n] <= commit_pos'[n]

CommitPosNeverDec ==
    [][commitPosNeverDecStep]_commit_pos

----------------------

CommitLogMatchingInv ==
    \A n1, n2 \in Node:
        LET
            min_pos == Min({commit_pos[n1], commit_pos[n2]})
        IN
            SubSeq(log[n1], 1, min_pos) = SubSeq(log[n2], 1, min_pos)

----------------------

GodLogMatchISR ==
    \A n \in Node:
        n \in global_config.isr =>
            /\ Len(god_log) <= Len(log[n])
            /\ god_log = SubSeq(log[n], 1, Len(god_log))

----------------------

GodLogLenMatchCommitPos ==
    \A n \in Node:
        isLocalLeader(n) =>
            commit_pos[n] <= Len(god_log)

----------------------

LocalNeedAddMatchConfig ==
    \A n \in Node:
        isLocalLeader(n) =>
            /\ local_need_add[n] \subseteq local_config[n].adding

----------------------

LocalAddingSetMatchLeaderPos ==
    \A n \in Node:
        LET
            pre_cond ==
                /\ isLocalLeader(n)
                /\ leader_syncing_nodes[n] = {}

            pos_map == leader_pos_map[n]

            adding_set ==
                local_config[n].adding \ local_need_add[n]

            cond ==
                \A x \in adding_set:
                    /\ pos_map[x] < commit_pos[n]
        IN
            pre_cond => cond

----------------------

LocalNeedAddAndSyncingNodes ==
    \A n \in Node:
        local_need_add[n] # {} => leader_syncing_nodes[n] = {}

----------------------

LeaderSyncingNodesInv ==
    \A n \in Node:
        local_config[n] # nil =>
            /\ leader_syncing_nodes[n] \subseteq local_config[n].isr
            /\ n \notin leader_syncing_nodes[n]

====

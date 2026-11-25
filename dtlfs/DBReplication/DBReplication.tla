---- MODULE DBReplication ----
EXTENDS TLC, Naturals, Sequences, FiniteSets

CONSTANTS Node, Value, nil, max_num_action

VARIABLES
    global_config,
    local_config, log,
    leader_pos_map, commit_pos,
    follower_ready, local_need_add,
    num_action

vars == <<
    global_config,
    local_config, log,
    leader_pos_map, commit_pos,
    follower_ready, local_need_add,
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
    /\ commit_pos \in [Node -> LogPos]
    /\ follower_ready \in [Node -> Null(BOOLEAN)]
    /\ local_need_add \in [Node -> SUBSET Node]

    /\ num_action \in 0..max_num_action

Init ==
    /\ \E nodes \in NonEmpty(Node): \E l \in nodes:
        /\ global_config = init_config(nodes, l)

    /\ local_config = [n \in Node |-> nil]
    /\ log = [n \in Node |-> <<>>]
    /\ leader_pos_map = [n \in Node |-> nil]
    /\ commit_pos = [n \in Node |-> 0]
    /\ follower_ready = [n \in Node |-> nil]
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

updateCommitPos(n, input_config) ==
    LET
        leader_pos == Len(log'[n])
        check_set == input_config.isr \ {n}
        repl_pos_list == {leader_pos_map'[n][x]: x \in check_set}
        new_pos == Min({leader_pos} \union repl_pos_list)
    IN
    /\ commit_pos' = [commit_pos EXCEPT ![n] = new_pos]

-------------------

updatePosMapDomain(n, new_domain, init_val) ==
    LET
        init_pos_map == [x \in new_domain |-> init_val]

        old_domain == DOMAIN leader_pos_map[n]

        update_fn(x, old) ==
            IF x \in old_domain
                THEN old
                ELSE 0

        do_update(old_map) ==
            [x \in new_domain |-> update_fn(x, old_map[x])]
    IN
    IF leader_pos_map[n] = nil THEN
        leader_pos_map' = [leader_pos_map EXCEPT ![n] = init_pos_map]
    ELSE
        leader_pos_map' = [leader_pos_map EXCEPT ![n] = do_update(@)]

--------------------------------------------------------------

moveAddingToLocalNeedAdd(n, conf) ==
    LET
        pos_map == leader_pos_map'[n]

        allow_move(x) ==
            pos_map[x] >= commit_pos'[n]

        move_set == {x \in conf.adding: allow_move(x)}

        new_conf == [conf EXCEPT
            !.adding = @ \ move_set,
            !.isr = @ \union move_set
        ]
    IN
    /\ local_config' = [local_config EXCEPT ![n] = new_conf]
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
        pos_map_domain == computePosMapDomain(n, isr, conf.adding)
        init_pos_map == [x \in pos_map_domain |-> commit_pos[n]]

        on_leader_epoch_changed ==
            /\ follower_ready' = [follower_ready EXCEPT ![n] = nil]

        on_leader_epoch_not_changed ==
            /\ UNCHANGED follower_ready

        on_leader ==
            /\ updatePosMapDomain(n, pos_map_domain, commit_pos[n])
            /\ updateCommitPos(n, conf)
            /\ IF epoch_changed
                THEN on_leader_epoch_changed
                ELSE on_leader_epoch_not_changed
            /\ moveAddingToLocalNeedAdd(n, conf)

        on_follower_epoch_changed ==
            /\ leader_pos_map' = [leader_pos_map EXCEPT ![n] = nil]
            /\ follower_ready' = [follower_ready EXCEPT ![n] = FALSE]
            /\ local_need_add' = [local_need_add EXCEPT ![n] = {}]
            /\ UNCHANGED commit_pos

        on_follower_epoch_not_changed ==
            /\ UNCHANGED leader_pos_map
            /\ UNCHANGED follower_ready
            /\ UNCHANGED local_need_add

        on_follower ==
            /\ local_config' = [local_config EXCEPT ![n] = conf]
            /\ IF epoch_changed
                THEN on_follower_epoch_changed
                ELSE on_follower_epoch_not_changed
            /\ UNCHANGED commit_pos
    IN
    /\ local_config[n] # nil => local_config[n].revision < revision

    /\ UNCHANGED log
    /\ IF conf.leader = n
        THEN on_leader
        ELSE on_follower

    /\ UNCHANGED num_action
    /\ UNCHANGED global_config

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
    /\ updateCommitPos(n, local_config[n])

    /\ UNCHANGED local_need_add
    /\ UNCHANGED follower_ready
    /\ UNCHANGED local_config
    /\ UNCHANGED global_config

--------------------------------------------------------------

getFollowerSetOf(l) ==
    local_config[l].isr \union local_config[l].adding

--------------------------------------------------------------

isFollowerOf(l, n) ==
    /\ isLocalLeader(l)
    /\ n \in getFollowerSetOf(l)
    /\ n # l
    /\ local_config[n] # nil
    /\ local_config[n].epoch = local_config[l].epoch

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

    /\ UNCHANGED local_need_add
    /\ UNCHANGED commit_pos
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
    /\ UNCHANGED follower_ready
    /\ UNCHANGED commit_pos
    /\ UNCHANGED local_need_add
    /\ configUnchanged

--------------------------------------------------------------

IncLeaderLogPos(l, n) ==
    LET
        pos == Len(log[n])
    IN
    /\ isFollowerOf(l, n)
    /\ follower_ready[n]
    /\ leader_pos_map[l][n] < pos

    /\ leader_pos_map' = [leader_pos_map EXCEPT ![l][n] = pos]
    /\ UNCHANGED log
    /\ updateCommitPos(l, local_config[l])
    /\ moveAddingToLocalNeedAdd(l, local_config[l])

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
    /\ UNCHANGED log
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
    /\ UNCHANGED local_need_add
    /\ UNCHANGED log

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

    /\ UNCHANGED follower_ready
    /\ UNCHANGED leader_pos_map
    /\ UNCHANGED num_action
    /\ UNCHANGED log
    /\ UNCHANGED local_config
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
        /\ isLocalFollower(n) => follower_ready[n] \in BOOLEAN
        /\ isLocalFollower(n) => local_need_add[n] = {}

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
        isr == local_config[n].isr \ {n}
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

LocalNeedAddMatchConfig ==
    \A n \in Node:
        local_config[n] # nil =>
            /\ local_need_add[n] \subseteq local_config[n].isr
            /\ local_need_add[n] \intersect local_config[n].adding = {}

----------------------

LocalNeedAddMatchLeaderPos ==
    \A n \in Node:
        LET
            pos_map == leader_pos_map[n]

            cond ==
                \A x \in local_config[n].adding:
                    pos_map[x] >= commit_pos[n] <=> x \in local_need_add[n]
        IN
        isLocalLeader(n) => cond

====

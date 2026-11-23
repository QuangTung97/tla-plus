---- MODULE DBReplication ----
EXTENDS TLC, Naturals, Sequences, FiniteSets

CONSTANTS Node, Value, nil, max_num_action

VARIABLES
    global_config,
    local_config, log,
    leader_pos_map, commit_pos,
    follower_ready,
    num_action

vars == <<
    global_config,
    local_config, log,
    leader_pos_map, commit_pos,
    follower_ready,
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

Revision == 20..(20 + max_num_action)

LogPos == 0..max_num_action

----------------------

Config == [
    epoch: Epoch,
    isr: NonEmpty(Node),
    leader: Node,
    revision: Revision
]

init_config(nodes, l) == [
    epoch |-> 10,
    isr |-> nodes,
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

    /\ num_action \in 0..max_num_action

Init ==
    /\ \E nodes \in NonEmpty(Node): \E l \in nodes:
        /\ global_config = init_config(nodes, l)

    /\ local_config = [n \in Node |-> nil]
    /\ log = [n \in Node |-> <<>>]
    /\ leader_pos_map = [n \in Node |-> nil]
    /\ commit_pos = [n \in Node |-> 0]
    /\ follower_ready = [n \in Node |-> nil]

    /\ num_action = 0

--------------------------------------------------------------

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

updateCommitPos(n) ==
    LET
        leader_pos == Len(log'[n])
        repl_pos_list == Range(leader_pos_map'[n])
        new_pos == Min({leader_pos} \union repl_pos_list)
    IN
    /\ commit_pos' = [commit_pos EXCEPT ![n] = new_pos]

-------------------

updatePosMapDomain(n, new_domain, default_val) ==
    LET
        init_pos_map == [x \in new_domain |-> default_val]

        old_domain == DOMAIN leader_pos_map[n]

        update_fn(x, old) ==
            IF x \in old_domain
                THEN old
                ELSE default_val

        do_update(old_map) ==
            [x \in new_domain |-> update_fn(x, old_map[x])]
    IN
    IF leader_pos_map[n] = nil THEN
        leader_pos_map' = [leader_pos_map EXCEPT ![n] = init_pos_map]
    ELSE
        leader_pos_map' = [leader_pos_map EXCEPT ![n] = do_update(@)]

--------------------------------------------------------------

SyncConfig(n) ==
    LET
        revision == global_config.revision

        epoch == global_config.epoch
        epoch_changed ==
            local_config[n] # nil =>
                local_config[n].epoch < global_config.epoch

        isr == global_config.isr
        pos_map_domain == isr \ {n}
        init_pos_map == [x \in pos_map_domain |-> commit_pos[n]]

        on_leader_epoch_changed ==
            /\ follower_ready' = [follower_ready EXCEPT ![n] = nil]

        on_leader ==
            /\ updatePosMapDomain(n, pos_map_domain, commit_pos[n])
            /\ updateCommitPos(n)
            /\ IF epoch_changed
                THEN on_leader_epoch_changed
                ELSE UNCHANGED follower_ready

        on_follower_epoch_changed ==
            /\ leader_pos_map' = [leader_pos_map EXCEPT ![n] = nil]
            /\ follower_ready' = [follower_ready EXCEPT ![n] = FALSE]
            /\ UNCHANGED commit_pos

        on_follower ==
            IF epoch_changed THEN
                on_follower_epoch_changed
            ELSE
                /\ UNCHANGED leader_pos_map
                /\ UNCHANGED follower_ready
                /\ UNCHANGED commit_pos
    IN
    /\ local_config[n] # nil => local_config[n].revision < revision
    /\ local_config' = [local_config EXCEPT ![n] = global_config]

    /\ UNCHANGED log
    /\ IF global_config.leader = n
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
    /\ updateCommitPos(n)

    /\ UNCHANGED follower_ready
    /\ UNCHANGED local_config
    /\ UNCHANGED global_config

--------------------------------------------------------------

isFollowerOf(l, n) ==
    /\ isLocalLeader(l)
    /\ n \in local_config[l].isr
    /\ n # l
    /\ local_config[n] # nil
    /\ local_config[n].epoch = local_config[l].epoch

--------------------------------------------------------------

TruncateFollowerLog(l, n) ==
    /\ isFollowerOf(l, n)
    /\ ~follower_ready[n]

    /\ follower_ready' = [follower_ready EXCEPT ![n] = TRUE]
    /\ UNCHANGED log \* TODO

    /\ UNCHANGED commit_pos
    /\ UNCHANGED leader_pos_map
    /\ UNCHANGED global_config
    /\ UNCHANGED local_config
    /\ UNCHANGED num_action

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
    /\ UNCHANGED global_config
    /\ UNCHANGED local_config
    /\ UNCHANGED num_action

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
    /\ updateCommitPos(l)

    /\ UNCHANGED follower_ready
    /\ UNCHANGED num_action
    /\ UNCHANGED global_config
    /\ UNCHANGED local_config

--------------------------------------------------------------

IncFollowerCommitPos(l, n) ==
    /\ isFollowerOf(l, n)
    /\ follower_ready[n]
    /\ commit_pos[n] < commit_pos[l]

    /\ commit_pos' = [commit_pos EXCEPT ![n] = commit_pos[l]]

    /\ UNCHANGED follower_ready
    /\ UNCHANGED leader_pos_map
    /\ UNCHANGED log
    /\ UNCHANGED num_action
    /\ UNCHANGED global_config
    /\ UNCHANGED local_config

--------------------------------------------------------------

UpdateGlobalConfig(new_nodes) ==
    LET
        isr == global_config.isr
        new_isr == isr \intersect new_nodes

        \* TODO add syncing set

        new_epoch(l) ==
            IF l = global_config.leader
                THEN global_config.epoch
                ELSE global_config.epoch + 1 \* inc when leader change

        new_config(l) == [
            epoch |-> new_epoch(l),
            isr |-> new_isr,
            leader |-> l,
            revision |-> global_config.revision + 1
        ]
    IN
    /\ allowAction
    /\ isr # new_nodes
    /\ new_isr # {}

    /\ \E l \in new_isr:
        /\ global_config' = new_config(l)

    /\ UNCHANGED local_config
    /\ UNCHANGED commit_pos
    /\ UNCHANGED leader_pos_map
    /\ UNCHANGED follower_ready
    /\ UNCHANGED log

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
    \/ \E n \in Node, v \in Value:
        \/ AddEntry(n, v)
    \/ \E l \in Node, n \in Node:
        \/ TruncateFollowerLog(l, n)
        \/ RecvEntry(l, n)
        \/ IncLeaderLogPos(l, n)
        \/ IncFollowerCommitPos(l, n)
    \/ \E nodes \in NonEmpty(Node):
        \/ UpdateGlobalConfig(nodes)
    \/ Terminated

Spec == Init /\ [][Next]_vars

--------------------------------------------------------------

LeaderInv ==
    \A n \in Node:
        /\ isLocalLeader(n) <=> leader_pos_map[n] # nil
        /\ isLocalLeader(n) => follower_ready[n] = nil

----------------------

LogPosInv ==
    \A n \in Node: \A pos \in DOMAIN log[n]:
        log[n][pos].pos = pos

----------------------

LeaderPosMapInv ==
    \A n \in Node:
        isLocalLeader(n) =>
            DOMAIN leader_pos_map[n] = local_config[n].isr \ {n}

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

====

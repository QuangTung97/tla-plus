---- MODULE DBReplV2 ----
EXTENDS TLC, Naturals, Sequences, FiniteSets

CONSTANTS Node, Value, max_num_action, nil

VARIABLES
    global_config,
    local_config, local_epoch,
    log, god_log,
    commit_pos, retention_pos,
    leader_pos_map, leader_syncing,
    leader_need_add,
    num_action

vars == <<
    global_config,
    local_config, local_epoch,
    log, god_log,
    commit_pos, retention_pos,
    leader_pos_map, leader_syncing,
    leader_need_add,
    num_action
>>

----------------------------------------------------------------------

NonEmpty(S) == (SUBSET S) \ {{}}

ASSUME NonEmpty({11, 12}) = {{11}, {12}, {11, 12}}

Null(S) == S \union {nil}

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

        on_follower ==
            /\ TRUE
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

TerminateCond ==
    /\ TRUE

Terminated ==
    /\ TerminateCond
    /\ UNCHANGED vars

----------------------------------------------------------------------

Next ==
    \/ \E n \in Node:
        \/ SyncConfig(n)
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

\* TODO inv between commit pos and retention pos

====

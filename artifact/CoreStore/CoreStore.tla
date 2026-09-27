---- MODULE CoreStore ----
EXTENDS TLC, Naturals, Sequences, FiniteSets

CONSTANTS Node, File, Value, nil

VARIABLES
    global_config,
    node_epoch, node_config, node_log,
    replicated_pos, commit_pos,
    node_mem_file, node_db_file, disk_file

global_vars == <<
    global_config
>>

node_vars == <<
    node_epoch, node_config, node_log,
    replicated_pos, commit_pos,
    node_mem_file, node_db_file, disk_file
>>

vars == <<
    global_vars,
    node_vars
>>

----------------------------------------------------------------------

Null(S) == S \union {nil}

NonEmpty(S) == (SUBSET S) \ {{}}

ASSUME NonEmpty({1, 2}) = {{1}, {2}, {1, 2}}

Max(S) == CHOOSE x \in S: (\A y \in S: y <= x)

ASSUME Max({11, 12, 13}) = 13

Min(S) == CHOOSE x \in S: (\A y \in S: y >= x)

ASSUME Min({11, 12, 13}) = 11

----------------------------------------------------------------------

Epoch == 10..19

Version == 1..9

Config == [
    epoch: Epoch,
    isr: NonEmpty(Node),
    leader: Node
]

LogEntry ==
    LET
        add_file == [
            type: {"AddFile"},
            epoch: Epoch,
            file: File,
            version: Version
        ]

        remove_file == [
            type: {"RemoveFile"},
            epoch: Epoch,
            file: File,
            version: Version
        ]

        finish_add == [
            type: {"FinishAdd"},
            epoch: Epoch,
            file: File,
            version: Version
        ]
    IN
        UNION {add_file, remove_file, finish_add}

MemFile == [
    value: Value,
    log_pos: Nat,
    committed: BOOLEAN,
    num_need_sync: Nat,
    num_synced: Nat
]

----------------------------------------------------------------------

TypeOK ==
    /\ global_config \in Config

    /\ node_epoch \in [Node -> Epoch]
    /\ node_config \in [Node -> Null(Config)]
    /\ node_log \in [Node -> Seq(LogEntry)]
    /\ replicated_pos \in [Node -> Null([Node -> Nat])]
    /\ commit_pos \in [Node -> Null(Nat)]

    /\ node_mem_file \in [Node -> [File -> Null(MemFile)]]
    /\ node_db_file \in [Node -> [File -> Null(Value)]]
    /\ disk_file \in [Node -> [File -> Null(Value)]]

Init ==
    /\ \E isr \in NonEmpty(Node): \E leader \in isr:
        global_config = [
            epoch |-> 10,
            isr |-> isr,
            leader |-> leader
        ]

    /\ node_epoch = [n \in Node |-> 10]
    /\ node_config = [n \in Node |-> nil]
    /\ node_log = [n \in Node |-> <<>>]
    /\ replicated_pos = [n \in Node |-> nil]
    /\ commit_pos = [n \in Node |-> nil]

    /\ node_mem_file = [n \in Node |-> [f \in File |-> nil]]
    /\ node_db_file = [n \in Node |-> [f \in File |-> nil]]
    /\ disk_file = [n \in Node |-> [f \in File |-> nil]]

----------------------------------------------------------------------

set_local(n, var, x) ==
    var' = [var EXCEPT ![n] = x]

----------------------------------------------------------------------

SyncConfig(n) ==
    LET
        init_pos == [n1 \in Node |-> 0] \* TODO flush pos

        on_leader ==
            /\ replicated_pos' = [replicated_pos EXCEPT ![n] = init_pos]
            /\ commit_pos' = [commit_pos EXCEPT ![n] = 0] \* TODO

        on_follower ==
            /\ replicated_pos' = [replicated_pos EXCEPT ![n] = nil]
            /\ commit_pos' = [commit_pos EXCEPT ![n] = nil]
    IN
    /\ node_config[n] # nil => node_config[n].epoch < global_config.epoch
    /\ node_config' = [node_config EXCEPT ![n] = global_config]
    /\ IF global_config.leader = n
        THEN on_leader
        ELSE on_follower

    /\ UNCHANGED node_epoch
    /\ UNCHANGED node_log
    /\ UNCHANGED <<node_mem_file, node_db_file, disk_file>>
    /\ UNCHANGED global_vars

----------------------------------------------------------------------

update_commit_pos(l) ==
    LET
        replicated_set == {replicated_pos'[l][n]: n \in node_config[l].isr}

        new_pos == Min(replicated_set)
    IN
    /\ commit_pos' = [commit_pos EXCEPT ![l] = new_pos]

----------------------------------------------------------------------

AddFile(n, f, v) ==
    LET
        conf == node_config[n]

        entry == [
            type |-> "AddFile",
            epoch |-> conf.epoch,
            file |-> f,
            version |-> 1
        ]

        index == Len(node_log[n]) + 1

        mem_file == [
            value |-> v,
            log_pos |-> index,
            committed |-> FALSE,
            num_need_sync |-> 0,
            num_synced |-> 0
        ]
    IN
    /\ conf # nil
    /\ conf.leader = n
    /\ node_mem_file[n][f] = nil

    /\ node_log' = [node_log EXCEPT ![n] = Append(@, entry)]
    /\ node_mem_file' = [node_mem_file EXCEPT ![n][f] = mem_file]
    /\ replicated_pos' = [replicated_pos EXCEPT ![n][n] = index]
    /\ update_commit_pos(n)

    /\ UNCHANGED node_epoch
    /\ UNCHANGED node_db_file
    /\ UNCHANGED disk_file
    /\ UNCHANGED <<node_config>>
    /\ UNCHANGED global_vars

----------------------------------------------------------------------

ReplicateLog(l, n) ==
    LET
        conf == node_config[l]
        index == Len(node_log[n]) + 1
        entry == node_log[l][index]
    IN
    /\ l # n
    /\ conf # nil
    /\ conf.leader = l
    /\ n \in conf.isr
    /\ index <= Len(node_log[l])
    /\ node_epoch[n] <= node_epoch[l]

    /\ node_epoch' = [node_epoch EXCEPT ![n] = node_epoch[l]]
    /\ node_log' = [node_log EXCEPT ![n] = Append(@, entry)]

    /\ UNCHANGED node_mem_file
    /\ UNCHANGED replicated_pos
    /\ UNCHANGED commit_pos
    /\ UNCHANGED node_db_file
    /\ UNCHANGED node_config
    /\ UNCHANGED disk_file
    /\ UNCHANGED global_vars

----------------------------------------------------------------------

Terminated ==
    /\ FALSE
    /\ UNCHANGED vars

----------------------------------------------------------------------

Next ==
    \/ \E n \in Node:
        \/ SyncConfig(n)
    \/ \E n \in Node, f \in File, v \in Value:
        \/ AddFile(n, f, v)
    \/ \E l \in Node, n \in Node:
        \/ ReplicateLog(l, n)
    \/ Terminated

Spec == Init /\ [][Next]_vars

----------------------------------------------------------------------

ConfigEpochAndNodeEpochInv ==
    \A n \in Node:
        node_config[n] # nil =>
            node_config[n].epoch <= node_epoch[n]

------------------

LeaderFollowerInv ==
    \A n \in Node:
        node_config[n] # nil =>
            IF node_config[n].leader = n THEN
                /\ replicated_pos[n] # nil
                /\ commit_pos[n] # nil
            ELSE
                /\ replicated_pos[n] = nil
                /\ commit_pos[n] = nil

------------------

CommitPosMatchReplicatedPos ==
    \A l \in Node:
        LET
            replicated_set == {replicated_pos[l][n]: n \in node_config[l].isr}
        IN
        commit_pos[l] # nil =>
            commit_pos[l] = Min(replicated_set)


----------------------------------------------------------------------

Next2 == Next

====

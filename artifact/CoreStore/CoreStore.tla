---- MODULE CoreStore ----
EXTENDS TLC, Naturals, Sequences, FiniteSets

CONSTANTS Node, File, Value, nil

VARIABLES
    global_config,
    node_epoch, node_config, node_log,
    node_mem_file, node_db_file, disk_file

global_vars == <<
    global_config
>>

node_vars == <<
    node_epoch, node_config, node_log,
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

----------------------------------------------------------------------

Epoch == 10..19

Version == 1..9

Config == [
    epoch: Epoch,
    isr: NonEmpty(Node),
    primary: Node
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
    num_sync: Nat
]

----------------------------------------------------------------------

TypeOK ==
    /\ global_config \in Config

    /\ node_epoch \in [Node -> Epoch]
    /\ node_config \in [Node -> Null(Config)]
    /\ node_log \in [Node -> Seq(LogEntry)]

    /\ node_mem_file \in [Node -> [File -> Null(MemFile)]]
    /\ node_db_file \in [Node -> [File -> Null(Value)]]
    /\ disk_file \in [Node -> [File -> Null(Value)]]

Init ==
    /\ \E isr \in NonEmpty(Node): \E primary \in isr:
        global_config = [
            epoch |-> 10,
            isr |-> isr,
            primary |-> primary
        ]

    /\ node_epoch = [n \in Node |-> 10]
    /\ node_config = [n \in Node |-> nil]
    /\ node_log = [n \in Node |-> <<>>]

    /\ node_mem_file = [n \in Node |-> [f \in File |-> nil]]
    /\ node_db_file = [n \in Node |-> [f \in File |-> nil]]
    /\ disk_file = [n \in Node |-> [f \in File |-> nil]]

----------------------------------------------------------------------

set_local(n, var, x) ==
    var' = [var EXCEPT ![n] = x]

----------------------------------------------------------------------

SyncConfig(n) ==
    /\ node_config[n] # nil => node_config[n].epoch < global_config.epoch
    /\ node_config' = [node_config EXCEPT ![n] = global_config]

    /\ UNCHANGED node_epoch
    /\ UNCHANGED node_log
    /\ UNCHANGED <<node_mem_file, node_db_file, disk_file>>
    /\ UNCHANGED global_vars

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
            num_sync |-> 0
        ]
    IN
    /\ conf # nil
    /\ conf.primary = n
    /\ node_mem_file[n][f] = nil

    /\ node_log' = [node_log EXCEPT ![n] = Append(@, entry)]
    /\ node_mem_file' = [node_mem_file EXCEPT ![n][f] = mem_file]

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
    /\ conf.primary = l
    /\ n \in conf.isr
    /\ index <= Len(node_log[l])
    /\ node_epoch[n] <= node_epoch[l]

    /\ node_epoch' = [node_epoch EXCEPT ![n] = node_epoch[l]]
    /\ node_log' = [node_log EXCEPT ![n] = Append(@, entry)]

    /\ UNCHANGED node_mem_file
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

----------------------------------------------------------------------

Next2 == Next

====

---- MODULE CoreStore ----
EXTENDS TLC, Naturals, Sequences, FiniteSets

CONSTANTS Node, File, Value, nil

VARIABLES
    global_config,
    node_config, node_log,
    node_db_file, disk_file

global_vars == <<
    global_config
>>

node_vars == <<
    node_config, node_log,
    node_db_file, disk_file
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

----------------------------------------------------------------------

TypeOK ==
    /\ global_config \in Config

    /\ node_config \in [Node -> Null(Config)]
    /\ node_log \in [Node -> Seq(LogEntry)]

    /\ node_db_file \in [Node -> [File -> Null(Value)]]
    /\ disk_file \in [Node -> [File -> Null(Value)]]

Init ==
    /\ \E isr \in NonEmpty(Node): \E primary \in isr:
        global_config = [
            epoch |-> 10,
            isr |-> isr,
            primary |-> primary
        ]
    /\ node_config = [n \in Node |-> nil]
    /\ node_log = [n \in Node |-> <<>>]

    /\ node_db_file = [n \in Node |-> [f \in File |-> nil]]
    /\ disk_file = [n \in Node |-> [f \in File |-> nil]]

----------------------------------------------------------------------

set_local(n, var, x) ==
    var' = [var EXCEPT ![n] = x]

----------------------------------------------------------------------

SyncConfig(n) ==
    /\ node_config[n] # nil => node_config[n].epoch < global_config.epoch
    /\ node_config' = [node_config EXCEPT ![n] = global_config]

    /\ UNCHANGED <<node_log>>
    /\ UNCHANGED <<node_db_file, disk_file>>
    /\ UNCHANGED global_vars

----------------------------------------------------------------------

AddFile(n, f) ==
    LET
        conf == node_config[n]

        entry == [
            type |-> "AddFile",
            epoch |-> conf.epoch
        ]
    IN
    /\ conf # nil
    /\ conf.primary = n

    /\ node_log' = [node_log EXCEPT ![n] = Append(@, entry)]

    /\ UNCHANGED disk_file
    /\ UNCHANGED <<node_config>>
    /\ UNCHANGED global_vars

----------------------------------------------------------------------

Terminated ==
    /\ FALSE
    /\ UNCHANGED vars

----------------------------------------------------------------------

Next ==
    \/ \E n \in Node:
        \/ SyncConfig(n)
    \/ \E n \in Node, f \in File:
        \/ AddFile(n, f)
    \/ Terminated

Spec == Init /\ [][Next]_vars

----------------------------------------------------------------------

----------------------------------------------------------------------

Next2 == Next

====

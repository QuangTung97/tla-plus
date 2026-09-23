---- MODULE CoreFS ----
EXTENDS TLC, Naturals, Sequences, FiniteSets

CONSTANTS File, Disk, Value, Attr, nil

VARIABLES
    global_config, global_log,
    disk_config, disk_config_offset

global_vars == <<
    global_config, global_log
>>

disk_vars == <<
    disk_config, disk_config_offset
>>

vars == <<
    global_vars,
    disk_vars
>>

--------------------------------------------------------------------

Null(S) == S \union {nil}

SubSetNonEmpty(S) == (SUBSET S) \ {{}}

Epoch == 11..19

EntryConfig == [
    epoch: Epoch,
    disks: SubSetNonEmpty(Disk),
    primary: Disk
]

empty_config == [f \in File |-> nil]

init_config(disks, primary) == [
    epoch |-> 11,
    disks |-> disks,
    primary |-> primary
]

GlobalLogEntry == [
    type: {"Split"},
    parent: Null(File),
    file: File,
    sub_files: SubSetNonEmpty(File),
    config: EntryConfig
]

init_split_log_entry(root, config) == [
    type |-> "Split",
    parent |-> nil,
    file |-> root,
    sub_files |-> {root},
    config |-> config
]

--------------------------------------------------------------------

TypeOK ==
    /\ global_config \in [File -> Null(EntryConfig)]
    /\ global_log \in Seq(GlobalLogEntry)

    /\ disk_config \in [Disk -> [File -> Null(EntryConfig)]]
    /\ disk_config_offset \in [Disk -> Nat]

Init ==
    /\ \E root \in File, disks \in SubSetNonEmpty(Disk): \E primary \in disks:
        LET
            config == init_config(disks, primary)
        IN
        /\ global_config = [empty_config EXCEPT ![root] = config]
        /\ global_log = <<init_split_log_entry(root, config)>>

    /\ disk_config = [d \in Disk |-> empty_config]
    /\ disk_config_offset = [d \in Disk |-> 0]

--------------------------------------------------------------------

DiskSyncLog(d) ==
    LET
        offset == disk_config_offset[d] + 1
        entry == global_log[offset]
        root == entry.file
    IN
    /\ disk_config_offset[d] < Len(global_log)

    /\ disk_config_offset' = [disk_config_offset EXCEPT ![d] = @ + 1]
    /\ disk_config' = [disk_config EXCEPT ![d][root] = entry.config]

    /\ UNCHANGED global_vars

--------------------------------------------------------------------

Terminated ==
    /\ UNCHANGED vars

--------------------------------------------------------------------

Next ==
    \/ \E d \in Disk:
        \/ DiskSyncLog(d)
    \/ Terminated

Spec == Init /\ [][Next]_vars

--------------------------------------------------------------------

====

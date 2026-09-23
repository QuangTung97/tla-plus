---- MODULE CoreFS ----
EXTENDS TLC, Naturals, Sequences, FiniteSets

CONSTANTS File, Disk, Value, Attr, nil

VARIABLES
    global_config, global_log,
    disk_config, disk_config_offset,
    created_files,
    file_config

global_vars == <<
    global_config, global_log
>>

disk_vars == <<
    disk_config, disk_config_offset
>>

file_vars == <<
    file_config
>>

vars == <<
    global_vars,
    disk_vars,
    created_files,
    file_vars
>>

--------------------------------------------------------------------

Null(S) == S \union {nil}

SubSetNonEmpty(S) == (SUBSET S) \ {{}}

Epoch == 11..19

DiskFile == Disk \X File

EntryConfig == [
    epoch: Epoch,
    disks: SubSetNonEmpty(Disk),
    primary: Disk
]

DiskEntryConfig == [
    epoch: Epoch,
    disks: SubSetNonEmpty(Disk),
    primary: Disk,
    state: {"Ready", "SetupNew", "Unused"},
    split_from: Null(File)
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

FileConfig == [
    sub_files: SUBSET File
]

--------------------------------------------------------------------

TypeOK ==
    /\ global_config \in [File -> Null(EntryConfig)]
    /\ global_log \in Seq(GlobalLogEntry)

    /\ disk_config \in [Disk -> [File -> Null(DiskEntryConfig)]]
    /\ disk_config_offset \in [Disk -> Nat]

    /\ created_files \subseteq File

    /\ file_config \in [DiskFile -> Null(FileConfig)]

Init ==
    /\ \E root \in File, disks \in SubSetNonEmpty(Disk): \E primary \in disks:
        LET
            config == init_config(disks, primary)
        IN
        /\ global_config = [empty_config EXCEPT ![root] = config]
        /\ global_log = <<init_split_log_entry(root, config)>>
        /\ created_files = {root}

    /\ disk_config = [d \in Disk |-> empty_config]
    /\ disk_config_offset = [d \in Disk |-> 0]

    /\ file_config = [df \in DiskFile |-> nil]

--------------------------------------------------------------------

DiskSyncLog(d) ==
    LET
        offset == disk_config_offset[d] + 1
        entry == global_log[offset]
        root == entry.file

        in_list == d \in entry.config.disks

        conf == [
            epoch |-> entry.config.epoch,
            disks |-> entry.config.disks,
            primary |-> entry.config.primary,
            state |-> IF in_list THEN "SetupNew" ELSE "Unused",
            split_from |-> entry.parent
        ]
    IN
    /\ disk_config_offset[d] < Len(global_log)

    /\ disk_config_offset' = [disk_config_offset EXCEPT ![d] = @ + 1]

    /\ entry.type = "Split"
    /\ disk_config' = [disk_config EXCEPT ![d][root] = conf]

    /\ UNCHANGED global_vars
    /\ UNCHANGED created_files
    /\ UNCHANGED file_vars

--------------------------------------------------------------------

DiskHandleSetupNew(d, f) ==
    LET
        df == <<d, f>>
        conf == disk_config[d][f]

        init_file_config == [
            sub_files |-> {}
        ]
    IN
    /\ conf # nil
    /\ conf.state = "SetupNew"
    /\ d = conf.primary

    /\ file_config' = [file_config EXCEPT ![df] = init_file_config]
    /\ disk_config' = [disk_config EXCEPT ![d][f].state = "Ready"]

    /\ UNCHANGED global_vars
    /\ UNCHANGED disk_config_offset
    /\ UNCHANGED created_files

--------------------------------------------------------------------

Terminated ==
    /\ \A d \in Disk, f \in File:
        disk_config[d][f] # nil =>
            IF d \in disk_config[d][f].disks THEN
               /\ disk_config[d][f].split_from = nil
               /\ disk_config[d][f].state = "Ready"
            ELSE
               /\ disk_config[d][f].split_from = nil
               /\ disk_config[d][f].state = "Unused"
    /\ UNCHANGED vars

--------------------------------------------------------------------

Next ==
    \/ \E d \in Disk:
        \/ DiskSyncLog(d)
    \/ \E d \in Disk, f \in File:
        \/ DiskHandleSetupNew(d, f)
    \/ Terminated

Spec == Init /\ [][Next]_vars

--------------------------------------------------------------------

====

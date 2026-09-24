---- MODULE CoreFS ----
EXTENDS TLC, Naturals, Sequences, FiniteSets

CONSTANTS File, Disk, Value, Attr, nil

VARIABLES
    global_config, global_log,
    disk_config, disk_config_offset,
    created_files,
    file_config, file_mem_config,
    file_log, file_written_pos, file_commit_pos

global_vars == <<
    global_config, global_log
>>

disk_vars == <<
    disk_config, disk_config_offset
>>

file_vars == <<
    file_config, file_mem_config,
    file_log, file_written_pos, file_commit_pos
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
    epoch: Epoch
]

FileLogEntry ==
    LET
        setup_new == [
            type: {"SetupNew"},
            config: FileConfig
        ]
    IN
    UNION {setup_new}

--------------------------------------------------------------------

TypeOK ==
    /\ global_config \in [File -> Null(EntryConfig)]
    /\ global_log \in Seq(GlobalLogEntry)

    /\ disk_config \in [Disk -> [File -> Null(DiskEntryConfig)]]
    /\ disk_config_offset \in [Disk -> Nat]

    /\ created_files \subseteq File

    /\ file_config \in [DiskFile -> Null(FileConfig)]
    /\ file_mem_config \in [DiskFile -> Null(FileConfig)]
    /\ file_log \in [DiskFile -> Seq(FileLogEntry)]
    /\ file_written_pos \in [DiskFile -> Null([Disk -> Nat])]
    /\ file_commit_pos \in [DiskFile -> Nat]

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
    /\ file_mem_config = [df \in DiskFile |-> nil]
    /\ file_log = [df \in DiskFile |-> <<>>]
    /\ file_written_pos = [df \in DiskFile |-> nil]
    /\ file_commit_pos = [df \in DiskFile |-> 0]

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
        mem_conf == file_mem_config[df]

        init_file_config == [
            epoch |-> conf.epoch
        ]

        entry == [
            type |-> "SetupNew",
            config |-> init_file_config
        ]

        init_log_pos == [d1 \in Disk |-> 0]
    IN
    /\ conf # nil
    /\ conf.state = "SetupNew"
    /\ d = conf.primary
    /\ mem_conf # nil => mem_conf.epoch < conf.epoch

    /\ file_mem_config' = [file_mem_config EXCEPT ![df] = init_file_config]
    /\ file_log' = [file_log EXCEPT ![df] = Append(@, entry)]
    /\ file_written_pos' = [file_written_pos EXCEPT ![df] = init_log_pos]

    /\ UNCHANGED file_commit_pos
    /\ UNCHANGED file_config
    /\ UNCHANGED global_vars
    /\ UNCHANGED disk_vars
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

\* TODO primary log always longer than non primary
\* TODO written pos must always <= log
\* TODO commit pos <= written pos

====

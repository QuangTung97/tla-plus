---- MODULE CoreFS ----
EXTENDS TLC, Naturals, Sequences, FiniteSets

CONSTANTS File, Disk, Value, Attr, nil

VARIABLES
    global_config, global_log,
    disk_config, disk_config_offset,
    created_files,
    file_config, file_mem_config,
    file_log, file_written_pos, file_commit_pos, file_replicate_pos

global_vars == <<
    global_config, global_log
>>

disk_vars == <<
    disk_config, disk_config_offset
>>

file_vars == <<
    file_config, file_mem_config,
    file_log, file_written_pos, file_commit_pos, file_replicate_pos
>>

vars == <<
    global_vars,
    disk_vars,
    created_files,
    file_vars
>>

--------------------------------------------------------------------

Min(S) == CHOOSE x \in S: (\A y \in S: y >= x)

ASSUME Min({11, 12, 13}) = 11

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
    epoch: Epoch,
    disks: SubSetNonEmpty(Disk)
]

FileLogEntry ==
    LET
        setup_new == [
            type: {"SetupNew"},
            epoch: Epoch,
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
    /\ file_written_pos \in [DiskFile -> Nat]
    /\ file_commit_pos \in [DiskFile -> Nat]
    /\ file_replicate_pos \in [DiskFile -> Null([Disk -> Nat])]

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
    /\ file_written_pos = [df \in DiskFile |-> 0]
    /\ file_commit_pos = [df \in DiskFile |-> 0]
    /\ file_replicate_pos = [df \in DiskFile |-> nil]

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
            epoch |-> conf.epoch,
            disks |-> conf.disks
        ]

        entry == [
            type |-> "SetupNew",
            epoch |-> conf.epoch,
            config |-> init_file_config
        ]

        init_replicate_pos == [d1 \in Disk |-> 0]
    IN
    /\ conf # nil
    /\ conf.state = "SetupNew"
    /\ d = conf.primary \* only for primary
    /\ mem_conf # nil => mem_conf.epoch < conf.epoch

    /\ file_mem_config' = [file_mem_config EXCEPT ![df] = init_file_config]
    /\ file_log' = [file_log EXCEPT ![df] = Append(@, entry)]
    /\ file_replicate_pos' = [file_replicate_pos EXCEPT ![df] = init_replicate_pos]

    /\ UNCHANGED file_written_pos
    /\ UNCHANGED file_commit_pos
    /\ UNCHANGED file_config
    /\ UNCHANGED global_vars
    /\ UNCHANGED disk_vars
    /\ UNCHANGED created_files

--------------------------------------------------------------------

WriteLog(d, f) ==
    LET
        df == <<d, f>>
        conf == file_mem_config[df]

        replicate_pos_list == {file_replicate_pos'[df][d1]: d1 \in conf.disks}
        new_commit_pos == Min(replicate_pos_list)

        on_primary ==
            /\ file_replicate_pos' = [file_replicate_pos EXCEPT
                    ![df][d] = file_written_pos'[df]
                ]
            /\ file_commit_pos' = [file_commit_pos EXCEPT ![df] = new_commit_pos]

        on_secondary ==
            /\ TRUE
    IN
    /\ file_written_pos[df] < Len(file_log[df])

    /\ file_written_pos' = [file_written_pos EXCEPT ![df] = @ + 1]
    /\ IF conf # nil
        THEN on_primary
        ELSE on_secondary

    /\ UNCHANGED file_log
    /\ UNCHANGED file_config
    /\ UNCHANGED file_mem_config
    /\ UNCHANGED created_files
    /\ UNCHANGED disk_vars
    /\ UNCHANGED global_vars

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
        \/ WriteLog(d, f)
    \/ Terminated

Spec == Init /\ [][Next]_vars

--------------------------------------------------------------------

PrimaryReplicatePosAndCommitPos ==
    \A df \in DiskFile:
        LET
            conf == file_mem_config[df]
            d == df[1]

            pos_list == {file_replicate_pos[df][d1]: d1 \in conf.disks}

            cond ==
                /\ file_written_pos[df] = file_replicate_pos[df][d]
                /\ file_commit_pos[df] = Min(pos_list)
        IN
            conf # nil => cond

-----------------

FileLogInv ==
    \A df \in DiskFile:
        /\ file_written_pos[df] <= Len(file_log[df])
        /\ file_commit_pos[df] <= file_written_pos[df]

-----------------

\* TODO primary log always longer than non primary (when match epoch)

====

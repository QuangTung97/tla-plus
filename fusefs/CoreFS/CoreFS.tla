---- MODULE CoreFS ----
EXTENDS TLC, Naturals, Sequences, FiniteSets

CONSTANTS File, Disk, Value, Attr, nil

VARIABLES
    global_parent_file, global_config, global_log,
    file_content, disk_parent_file, disk_config,
    disk_log_offset

global_vars == <<
    global_parent_file, global_config, global_log
>>

disk_vars == <<
    file_content, disk_parent_file, disk_config,
    disk_log_offset
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

LogEntry ==
    LET
        split_entry == [
            type: {"Split"},
            file: File,
            prev: Null(File),
            disks: SubSetNonEmpty(Disk),
            primary: Disk
        ]
    IN
    UNION {split_entry}

init_entry_config == [f \in File |-> nil]

init_config(disks, primary) == [
    epoch |-> 11,
    disks |-> disks,
    primary |-> primary
]

init_log_entry(root, disks, primary) == [
    type |-> "Split",
    file |-> root,
    prev |-> nil,
    disks |-> disks,
    primary |-> primary
]

FileContent == [
    data: Value,
    attr: Attr
]

DiskFileContent == [File -> Null(FileContent)]

--------------------------------------------------------------------

TypeOK ==
    /\ global_parent_file \in [File -> File]
    /\ global_config \in [File -> Null(EntryConfig)]
    /\ global_log \in Seq(LogEntry)

    /\ file_content \in [Disk -> DiskFileContent]
    /\ disk_parent_file \in [Disk -> [File -> Null(File)]]
    /\ disk_config \in [Disk -> [File -> Null(EntryConfig)]]
    /\ disk_log_offset \in [Disk -> Nat]

Init ==
    /\ \E root \in File:
        /\ global_parent_file = [f \in File |-> root]
        /\ \E disks \in SubSetNonEmpty(Disk): \E primary \in disks:
            /\ global_config = [init_entry_config EXCEPT
                    ![root] = init_config(disks, primary)
                ]
            /\ global_log = <<init_log_entry(root, disks, primary)>>

    /\ file_content = [d \in Disk |-> [f \in File |-> nil]]
    /\ disk_parent_file = [d \in Disk |-> [f \in File |-> nil]]
    /\ disk_config = [d \in Disk |-> [f \in File |-> nil]]
    /\ disk_log_offset = [d \in Disk |-> 0]

--------------------------------------------------------------------

global_entry_files == {global_parent_file[f]: f \in File}

--------------------------------------------------------------------

UpdateFileData(d, f, v) ==
    LET
        root == disk_parent_file[d][f]
    IN
    /\ root # nil
    /\ file_content[f].data # v
    /\ file_content' = [file_content EXCEPT ![f].data = v]

--------------------------------------------------------------------

Terminated ==
    /\ UNCHANGED vars

--------------------------------------------------------------------

Next ==
    \/ \E d \in Disk, f \in File, v \in Value:
        \/ UpdateFileData(d, f, v)
    \/ Terminated

Spec == Init /\ [][Next]_vars

--------------------------------------------------------------------

EveryEntryFileHasConfig ==
    \A f \in global_entry_files: global_config[f] # nil

====

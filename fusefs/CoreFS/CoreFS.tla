---- MODULE CoreFS ----
EXTENDS TLC, Naturals, Sequences, FiniteSets

CONSTANTS File, Disk, Value, Attr, nil

VARIABLES
    global_parent_file, global_config, global_log,
    disk_file_mem, disk_file_content, disk_parent_file,
    disk_config, disk_global_offset,
    disk_mem_log, disk_log

global_vars == <<
    global_parent_file, global_config, global_log
>>

disk_vars == <<
    disk_file_mem, disk_file_content, disk_parent_file,
    disk_config, disk_global_offset,
    disk_mem_log, disk_log
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
            sub_files: SUBSET File,
            config: EntryConfig
        ]
    IN
    UNION {split_entry}

init_entry_config == [f \in File |-> nil]

init_config(disks, primary) == [
    epoch |-> 11,
    disks |-> disks,
    primary |-> primary
]

init_log_entry(root, config) == [
    type |-> "Split",
    file |-> root,
    prev |-> nil,
    sub_files |-> File,
    config |-> config
]

FileContent == [
    data: Value,
    attr: Attr
]

DiskFileContent == [File -> Null(FileContent)]

DiskLogEntry ==
    LET
        add_file == [
            type: {"AddFile"},
            file: File
        ]
    IN
    UNION {add_file}

--------------------------------------------------------------------

TypeOK ==
    /\ global_parent_file \in [File -> File]
    /\ global_config \in [File -> Null(EntryConfig)]
    /\ global_log \in Seq(LogEntry)

    /\ disk_file_content \in [Disk -> DiskFileContent]
    /\ disk_file_mem \in [Disk -> DiskFileContent]
    /\ disk_parent_file \in [Disk -> [File -> Null(File)]]
    /\ disk_config \in [Disk -> [File -> Null(EntryConfig)]]
    /\ disk_global_offset \in [Disk -> Nat]

    /\ disk_log \in [Disk -> Seq(DiskLogEntry)]
    /\ disk_mem_log \in [Disk -> Seq(DiskLogEntry)]

Init ==
    /\ \E root \in File:
        /\ global_parent_file = [f \in File |-> root]
        /\ \E disks \in SubSetNonEmpty(Disk): \E primary \in disks:
            LET
                config == init_config(disks, primary)
            IN
            /\ global_config = [init_entry_config EXCEPT ![root] = config]
            /\ global_log = <<init_log_entry(root, config)>>

    /\ disk_file_content = [d \in Disk |-> [f \in File |-> nil]]
    /\ disk_file_mem = [d \in Disk |-> [f \in File |-> nil]]

    /\ disk_parent_file = [d \in Disk |-> [f \in File |-> nil]]
    /\ disk_config = [d \in Disk |-> [f \in File |-> nil]]
    /\ disk_global_offset = [d \in Disk |-> 0]

    /\ disk_log = [d \in Disk |-> <<>>]
    /\ disk_mem_log = [d \in Disk |-> <<>>]

--------------------------------------------------------------------

global_entry_files == {global_parent_file[f]: f \in File}

--------------------------------------------------------------------

DiskSyncLog(d) ==
    LET
        offset == disk_global_offset[d] + 1
        entry == global_log[offset]
        root == entry.file

        update_parent_file(old) ==
            [f \in File |-> IF f \in entry.sub_files THEN root ELSE old[f]]
    IN
    /\ disk_global_offset[d] < Len(global_log)

    /\ disk_global_offset' = [disk_global_offset EXCEPT ![d] = @ + 1]
    /\ disk_config' = [disk_config EXCEPT ![d][root] = entry.config]
    /\ disk_parent_file' = [disk_parent_file EXCEPT ![d] = update_parent_file(@)]

    /\ UNCHANGED <<disk_file_content, disk_file_mem>>
    /\ UNCHANGED <<disk_log, disk_mem_log>>
    /\ UNCHANGED global_vars

--------------------------------------------------------------------

AddFile(d, f, v, a) ==
    LET
        root == disk_parent_file[d][f]
        content == disk_file_mem[d]
        primary == disk_config[d][root].primary

        file_data == [
            data |-> v,
            attr |-> a
        ]

        entry == [
            type |-> "AddFile",
            file |-> f
        ]
    IN
    /\ root # nil
    /\ content[f] = nil
    /\ primary = d

    /\ disk_file_mem' = [disk_file_mem EXCEPT ![d][f] = file_data]
    /\ disk_mem_log' = [disk_mem_log EXCEPT ![d] = Append(@, entry)]

    /\ UNCHANGED disk_log
    /\ UNCHANGED disk_config
    /\ UNCHANGED disk_global_offset
    /\ UNCHANGED disk_parent_file
    /\ UNCHANGED disk_file_content
    /\ UNCHANGED global_vars

--------------------------------------------------------------------

UpdateFileData(d, f, v) ==
    LET
        root == disk_parent_file[d][f]
        content == disk_file_content[d]
        primary == disk_config[d][root].primary
    IN
    /\ root # nil
    /\ content[f] # nil
    /\ content[f].data # v
    /\ primary = d

--------------------------------------------------------------------

Terminated ==
    /\ UNCHANGED vars

--------------------------------------------------------------------

Next ==
    \/ \E d \in Disk:
        \/ DiskSyncLog(d)
    \/ \E d \in Disk, f \in File, v \in Value, a \in Attr:
        \/ AddFile(d, f, v, a)
    \/ \E d \in Disk, f \in File, v \in Value:
        \/ UpdateFileData(d, f, v)
    \/ Terminated

Spec == Init /\ [][Next]_vars

--------------------------------------------------------------------

EveryEntryFileHasConfig ==
    \A f \in global_entry_files: global_config[f] # nil

====

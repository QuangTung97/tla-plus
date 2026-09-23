---- MODULE CoreFS ----
EXTENDS TLC, Naturals, Sequences, FiniteSets

CONSTANTS File, Disk, Value, Attr, nil

VARIABLES
    global_config, global_log,
    disk_config, disk_config_offset, disk_pending_actions,
    created_files

global_vars == <<
    global_config, global_log
>>

disk_vars == <<
    disk_config, disk_config_offset, disk_pending_actions
>>

vars == <<
    global_vars,
    disk_vars,
    created_files
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

DiskPendingAction == [
    type: {"Split"},
    parent: Null(File),
    file: File,
    state: {"Finishing"}
]

--------------------------------------------------------------------

TypeOK ==
    /\ global_config \in [File -> Null(EntryConfig)]
    /\ global_log \in Seq(GlobalLogEntry)

    /\ disk_config \in [Disk -> [File -> Null(EntryConfig)]]
    /\ disk_config_offset \in [Disk -> Nat]
    /\ disk_pending_actions \in [Disk -> Seq(DiskPendingAction)]

    /\ created_files \subseteq File

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
    /\ disk_pending_actions = [d \in Disk |-> <<>>]

--------------------------------------------------------------------

DiskSyncLog(d) ==
    LET
        offset == disk_config_offset[d] + 1
        entry == global_log[offset]
        root == entry.file

        action == [
            type |-> "Split",
            parent |-> nil,
            file |-> root,
            state |-> "Finishing"
        ]

        append_action ==
            disk_pending_actions' = [disk_pending_actions EXCEPT
                ![d] = Append(@, action)
            ]
    IN
    /\ disk_config_offset[d] < Len(global_log)

    /\ disk_config_offset' = [disk_config_offset EXCEPT ![d] = @ + 1]

    /\ entry.type = "Split"
    /\ disk_config' = [disk_config EXCEPT ![d][root] = entry.config]

    /\ IF d \in entry.config.disks
        THEN append_action
        ELSE UNCHANGED disk_pending_actions

    /\ UNCHANGED global_vars
    /\ UNCHANGED created_files

--------------------------------------------------------------------

DiskHandleAction(d) ==
    LET
        action == disk_pending_actions[d][1]

        remove_action ==
            disk_pending_actions' = [disk_pending_actions
                EXCEPT ![d] = Tail(@)
            ]
    IN
    /\ disk_pending_actions[d] # <<>>

    /\ action.type = "Split"
    /\ action.state = "Finishing"
    /\ remove_action

    /\ UNCHANGED global_vars
    /\ UNCHANGED <<disk_config, disk_config_offset>>
    /\ UNCHANGED created_files

--------------------------------------------------------------------

Terminated ==
    /\ \A d \in Disk:
        /\ disk_pending_actions[d] = <<>>
    /\ UNCHANGED vars

--------------------------------------------------------------------

Next ==
    \/ \E d \in Disk:
        \/ DiskSyncLog(d)
        \/ DiskHandleAction(d)
    \/ Terminated

Spec == Init /\ [][Next]_vars

--------------------------------------------------------------------

====

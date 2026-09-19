---- MODULE CoreFS ----
EXTENDS TLC, Naturals, Sequences, FiniteSets

CONSTANTS File, Disk, Value, Attr, nil

VARIABLES
    parent_file, file_content, entry_config

vars == <<
    parent_file, file_content, entry_config
>>

--------------------------------------------------------------------

Null(S) == S \union {nil}

SubSetNonEmpty(S) == (SUBSET S) \ {{}}

FileContent == [
    data: Value,
    attr: Attr
]

Epoch == 11..19

EntryConfig == [
    epoch: Epoch,
    disks: SubSetNonEmpty(Disk)
]

init_entry_config == [f \in File |-> nil]

init_config(disks) == [
    epoch |-> 11,
    disks |-> disks
]

--------------------------------------------------------------------

TypeOK ==
    /\ parent_file \in [File -> File]
    /\ file_content \in [File -> Null(FileContent)]
    /\ entry_config \in [File -> Null(EntryConfig)]

Init ==
    /\ \E root \in File:
        /\ parent_file = [f \in File |-> root]
        /\ \E disks \in SubSetNonEmpty(Disk):
            entry_config = [init_entry_config EXCEPT ![root] = init_config(disks)]
    /\ file_content = [f \in File |-> nil]

--------------------------------------------------------------------

entry_files == {parent_file[f]: f \in File}

--------------------------------------------------------------------

Terminated ==
    /\ UNCHANGED vars

--------------------------------------------------------------------

Next ==
    \/ Terminated

Spec == Init /\ [][Next]_vars

--------------------------------------------------------------------

EveryEntryFileHasConfig ==
    \A f \in entry_files: entry_config[f] # nil

====

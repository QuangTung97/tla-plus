------ MODULE USSRemoveEmpty ----
EXTENDS TLC, Naturals, Sequences

CONSTANTS nil, max_num_clear

VARIABLES core_db, master_db, slave_db, allow_write, num_clear

vars == <<core_db, master_db, slave_db, allow_write, num_clear>>

-----------------------------------------------------

Entry == [
    status: {"Empty", "Writing"},
    mark_delete: BOOLEAN
]

NullEntry == Entry \union {nil}

-----------------------------------------------------

TypeOK ==
    /\ core_db \in NullEntry
    /\ master_db \in NullEntry
    /\ slave_db \in {"Writing", nil}
    /\ allow_write \in BOOLEAN
    /\ num_clear \in 0..max_num_clear

Init ==
    /\ core_db = nil
    /\ master_db = nil
    /\ slave_db = nil
    /\ allow_write \in BOOLEAN
    /\ num_clear = 0

-----------------------------------------------------

core_unchanged ==
    /\ UNCHANGED master_db
    /\ UNCHANGED slave_db
    /\ UNCHANGED allow_write
    /\ UNCHANGED num_clear

NewEntry ==
    LET
        e == [
            status |-> "Empty",
            mark_delete |-> FALSE
        ]
    IN
    /\ core_db = nil
    /\ core_db' = e
    /\ core_unchanged


MarkReadyDelete ==
    /\ core_db # nil
    /\ core_db.status = "Empty"
    /\ core_db' = [core_db EXCEPT !.mark_delete = TRUE]
    /\ core_unchanged


MasterSync ==
    /\ master_db # core_db
    /\ master_db' = core_db
    /\ UNCHANGED core_db
    /\ UNCHANGED slave_db
    /\ UNCHANGED allow_write
    /\ UNCHANGED num_clear


WriteToSlave ==
    /\ allow_write
    /\ master_db # nil
    /\ master_db.mark_delete = FALSE \* Not mark deleted
    /\ slave_db = nil

    /\ slave_db' = "Writing"

    /\ UNCHANGED master_db
    /\ UNCHANGED core_db
    /\ UNCHANGED allow_write
    /\ UNCHANGED num_clear


SlaveSyncToCore ==
    /\ slave_db = "Writing"
    /\ core_db.status = "Empty"
    /\ core_db' = [core_db EXCEPT
            !.status = "Writing",
            !.mark_delete = FALSE
        ]
    /\ UNCHANGED master_db
    /\ UNCHANGED slave_db
    /\ UNCHANGED allow_write
    /\ UNCHANGED num_clear


--------------------------

DeleteEntry ==
    /\ core_db # nil
    /\ core_db.mark_delete

    /\ ~(ENABLED MasterSync) \* Watch when no update on master
    /\ ~(ENABLED SlaveSyncToCore) \* Watch when no update on slave

    /\ core_db' = nil
    /\ core_unchanged


ClearMarkDelete ==
    /\ allow_write
    /\ core_db # nil
    /\ core_db.mark_delete

    /\ num_clear < max_num_clear
    /\ num_clear' = num_clear + 1

    /\ core_db' = [core_db EXCEPT !.mark_delete = FALSE]

    /\ UNCHANGED master_db
    /\ UNCHANGED slave_db
    /\ UNCHANGED allow_write

-----------------------------------------------------

TerminateCond ==
    LET
        written ==
            /\ allow_write
            /\ slave_db = "Writing"
            /\ core_db # nil
            /\ core_db.status = "Writing"

        deleted ==
            /\ core_db = nil
            /\ slave_db = nil
    IN
    /\ \/ written
       \/ deleted


Terminated ==
    /\ TerminateCond
    /\ UNCHANGED vars


Next ==
    \/ NewEntry
    \/ MarkReadyDelete
    \/ DeleteEntry
    \/ ClearMarkDelete

    \/ MasterSync
    \/ WriteToSlave
    \/ SlaveSyncToCore

    \/ Terminated

Spec == Init /\ [][Next]_vars

FairSpec == Spec /\ WF_vars(Next)

-----------------------------------------------------

AlwaysTerminate == []<>TerminateCond


NotWritingWhenEntryDeleted ==
    core_db = nil => slave_db = nil

====

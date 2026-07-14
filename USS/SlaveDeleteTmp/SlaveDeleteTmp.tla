---- MODULE SlaveDeleteTmp ----
EXTENDS TLC, Naturals

CONSTANTS nil, Node

VARIABLES
    pc, state, disk, need_delete, background_pc

vars == <<
    pc, state, disk, need_delete, background_pc
>>

---------------------------------------------------------------------

DiskValue == 20..29

Disk == [
    value: DiskValue,
    with_temp: BOOLEAN
]

PC == {"Init", "WriteComplete", "Terminated"}

BackgroundPC == {"Init", "DeleteTmp"}

---------------------------------------------------------------------

TypeOK ==
    /\ pc \in [Node -> PC]
    /\ state \in {"Init", "Writing", "Completed"}
    /\ disk \in Disk
    /\ need_delete \in BOOLEAN
    /\ background_pc \in BackgroundPC

Init ==
    /\ pc = [n \in Node |-> "Init"]
    /\ state = "Init"
    /\ disk = [value |-> 20, with_temp |-> FALSE]
    /\ need_delete = FALSE
    /\ background_pc = "Init"

---------------------------------------------------------------------

goto(n, l) ==
    pc' = [pc EXCEPT ![n] = l]

WriteData(n, with_temp) ==
    /\ pc[n] = "Init"
    /\ state \in {"Init", "Completed"}
    /\ state' = "Writing"
    /\ goto(n, "WriteComplete")
    /\ disk' = [disk EXCEPT !.value = @ + 1, !.with_temp = with_temp]
    /\ UNCHANGED background_pc
    /\ UNCHANGED need_delete

-----------------------

WriteComplete(n) ==
    /\ pc[n] = "WriteComplete"
    /\ goto(n, "Terminated")
    /\ state' = "Completed"
    /\ need_delete' = disk.with_temp
    /\ UNCHANGED disk
    /\ UNCHANGED background_pc

---------------------------------------------------------------------

StartDeleteBackground ==
    /\ need_delete
    /\ state \in {"Completed"}
    /\ background_pc = "Init"
    /\ background_pc' = "DeleteTmp"
    /\ state' = "Writing"

    /\ UNCHANGED pc
    /\ UNCHANGED need_delete
    /\ UNCHANGED disk

-----------------------

DoDelete ==
    /\ background_pc = "DeleteTmp"
    /\ background_pc' = "Init"
    /\ disk' = [disk EXCEPT !.with_temp = FALSE]
    /\ need_delete' = FALSE
    /\ state' = "Completed"
    /\ UNCHANGED pc

---------------------------------------------------------------------

TerminateCond ==
    /\ \A n \in Node: pc[n] = "Terminated"
    /\ disk.with_temp = FALSE
    /\ need_delete = FALSE
    /\ background_pc = "Init"

Terminated ==
    /\ TerminateCond
    /\ UNCHANGED vars

-----------------------

Next ==
    \/ \E n \in Node, with_temp \in BOOLEAN: WriteData(n, with_temp)
    \/ \E n \in Node:
        \/ WriteComplete(n)
    \/ StartDeleteBackground
    \/ DoDelete
    \/ Terminated

Spec == Init /\ [][Next]_vars

FairSpec == Spec /\ WF_vars(Next)

---------------------------------------------------------------------

AlwaysTerminated == []<>TerminateCond


NotAllowDeleteRaceWithWrite ==
    LET
        is_normal_writing ==
            \E n \in Node: pc[n] = "WriteComplete"

        cond ==
            /\ is_normal_writing
            /\ background_pc = "DeleteTmp"
    IN
        ~cond

====

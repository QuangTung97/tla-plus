------ MODULE WAL ----
EXTENDS TLC, Naturals

CONSTANTS Node, num_page

VARIABLES pc, wal

vars == <<pc, wal>>

--------------------------------------------------------------------------

Value == 21..25

PageIndex == 1..num_page

PageNum == 0..(3 * num_page)

Page == [
    num: PageNum
]

init_page == [
    num |-> 0
]

PC == {"Init", "Terminated"}

--------------------------------------------------------------------------

TypeOK ==
    /\ wal \in [PageIndex -> Page]
    /\ pc \in [Node -> PC]

Init ==
    /\ wal = [x \in PageIndex |-> init_page]
    /\ pc = [n \in Node |-> "Init"]

--------------------------------------------------------------------------

Terminated ==
    /\ UNCHANGED vars

Next ==
    \/ Terminated

Spec == Init /\ [][Next]_vars

====

---- MODULE Downloader ----
EXTENDS TLC, Naturals, FiniteSets, Sequences

CONSTANTS Node, nil

VARIABLES
    last_file_id, store,
    pc, local_id,
    writer_pc

local_vars == <<pc, local_id>>

vars == <<
    last_file_id, store,
    local_vars,
    writer_pc
>>

--------------------------------------------------------------------

Null(S) == S \union {nil}

num_nodes == Cardinality(Node)

FileID == 20..(20 + num_nodes)

PC == {"Init", "StartWriter", "WaitFinish", "Terminated"}

FileState == [
    status: {"Init", "Writing", "Canceled", "Finished"}
]

WriterPC == {"Init", "Writing", "Terminated"}

--------------------------------------------------------------------

TypeOK ==
    /\ pc \in [Node -> PC]
    /\ local_id \in [Node -> Null(FileID)]

    /\ last_file_id \in FileID
    /\ store \in [FileID -> Null(FileState)]
    /\ writer_pc \in [FileID -> WriterPC]

Init ==
    /\ pc = [n \in Node |-> "Init"]
    /\ local_id = [n \in Node |-> nil]

    /\ last_file_id = 20
    /\ store = [id \in FileID |-> nil]
    /\ writer_pc = [id \in FileID |-> "Init"]

--------------------------------------------------------------------

goto(n, l) ==
    pc' = [pc EXCEPT ![n] = l]

set_local(n, var, x) ==
    var' = [var EXCEPT ![n] = x]

------------------------------

StartDownload(n) ==
    LET
        id == last_file_id + 1
        state == [
            status |-> "Init"
        ]
    IN
    /\ pc[n] = "Init"

    /\ last_file_id' = id
    /\ store' = [store EXCEPT ![id] = state]
    /\ writer_pc' = [writer_pc EXCEPT ![id] = "Writing"]
    /\ goto(n, "StartWriter")
    /\ set_local(n, local_id, id)

--------------------------------------------------------------------

StartWriter(n) ==
    LET
        id == local_id[n]

        exist_id ==
            /\ store[id] # nil
            /\ store[id].status = "Init"

        on_normal ==
            /\ goto(n, "WaitFinish")
            /\ store' = [store EXCEPT ![id].status = "Writing"]

        on_not_found ==
            /\ goto(n, "Terminated")
            /\ UNCHANGED store
    IN
    /\ pc[n] = "StartWriter"

    /\ IF exist_id
        THEN on_normal
        ELSE on_not_found

    /\ UNCHANGED local_id
    /\ UNCHANGED writer_pc
    /\ UNCHANGED last_file_id

--------------------------------------------------------------------

WriteData(id) ==
    LET
        wait_cond ==
            store[id].status = "Init"

        on_normal ==
            /\ store' = [store EXCEPT ![id].status = "Finished"]

        on_canceled ==
            /\ store' = [store EXCEPT ![id] = nil]
    IN
    /\ writer_pc[id] = "Writing"
    /\ ~wait_cond

    /\ IF store[id].status = "Canceled"
        THEN on_canceled
        ELSE on_normal
    /\ writer_pc' = [writer_pc EXCEPT ![id] = "Terminated"]

    /\ UNCHANGED local_vars
    /\ UNCHANGED last_file_id

--------------------------------------------------------------------

WaitFinish(n) ==
    LET
        id == local_id[n]
    IN
    /\ pc[n] = "WaitFinish"
    /\ store[id].status = "Finished"

    /\ store' = [store EXCEPT ![id] = nil]
    /\ goto(n, "Terminated")
    /\ set_local(n, local_id, nil)

    /\ UNCHANGED writer_pc
    /\ UNCHANGED last_file_id

--------------------------------------------------------------------

NodeShutdown(n) ==
    /\ pc[n] \notin {"Init", "WaitFinish", "Terminated"}

    /\ goto(n, "Terminated")
    /\ set_local(n, local_id, nil)

    /\ UNCHANGED store
    /\ UNCHANGED writer_pc
    /\ UNCHANGED last_file_id

--------------------------------------------------------------------

LruDelete(id) ==
    /\ store[id] # nil
    /\ store[id].status = "Init"

    /\ store' = [store EXCEPT ![id].status = "Canceled"]

    /\ UNCHANGED writer_pc
    /\ UNCHANGED local_vars
    /\ UNCHANGED last_file_id

--------------------------------------------------------------------

TerminateCond ==
    /\ \A n \in Node: pc[n] = "Terminated"
    /\ \A id \in FileID:
        \/ writer_pc[id] = "Init"
        \/ writer_pc[id] = "Terminated"

Terminated ==
    /\ TerminateCond
    /\ UNCHANGED vars

--------------------------------------------------------------------

Next ==
    \/ \E n \in Node:
        \/ StartDownload(n)
        \/ StartWriter(n)
        \/ WaitFinish(n)
        \/ NodeShutdown(n)
    \/ \E id \in FileID:
        \/ WriteData(id)
        \/ LruDelete(id)
    \/ Terminated

Spec == Init /\ [][Next]_vars

FairSpec == Spec /\ WF_vars(Next)

--------------------------------------------------------------------

AlwaysTerminated == []<>TerminateCond

------------------------------

storeStatusStepFileID(id) ==
    LET
        to_init ==
            /\ store[id] = nil
            /\ store'[id] # nil
            /\ store'[id].status = "Init"

        to_writing ==
            /\ store[id] # nil
            /\ store[id].status = "Init"
            /\ store'[id] # nil
            /\ store'[id].status = "Writing"

        to_canceled ==
            /\ store[id] # nil
            /\ store[id].status = "Init"
            /\ store'[id] # nil
            /\ store'[id].status = "Canceled"

        to_finished ==
            /\ store[id] # nil
            /\ store[id].status = "Writing"
            /\ store'[id] # nil
            /\ store'[id].status = "Finished"

        to_null ==
            /\ store[id] # nil
            /\ store[id].status \in {"Canceled", "Finished"}
            /\ store'[id] = nil

        step_cond ==
            \/ to_init
            \/ to_writing
            \/ to_canceled
            \/ to_finished
            \/ to_null
    IN
        store[id] # store'[id] => step_cond

storeStatusStep ==
    \A id \in FileID: storeStatusStepFileID(id)

StoreStatusProperty ==
    [][storeStatusStep]_store

------------------------------

TerminatedInv ==
    LET
        cond ==
            /\ \A id \in FileID: store[id] = nil
    IN
        TerminateCond => cond

====

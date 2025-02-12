------ MODULE SlaveLogic ----
EXTENDS TLC, Naturals, Sequences, FiniteSets

CONSTANTS Node, Entry, User, nil, max_action, max_timeout

VARIABLES status, replica_status, dir_state,
    pc, local_req,
    request_queue, num_action

vars == <<status, replica_status, dir_state,
    pc, local_req,
    request_queue, num_action>>

-------------------------------------------------------
Status == {
    "None", "CreatingEntry", "Writing",
    "WriteTimeout", "WriteCompleted",
    "Synced"
}

ReplicaStatus == {"Empty", "Writing", "Written"}

DirState == [
    status: {"None", "Created"},
    writer: SUBSET User
]

PC == {
    "Init", "CreateDir", "AddWritePerm",
    "UpdateReplicaToWriting", "UpdateStatusToWriting",
    "UpdateToWriteTimeout", "UpdateToWriteCompleted",
    "SyncToWritten",
    "UpdateToSynced"
}

WriteReq == [type: {"Write"}, entry: Entry, user: User]

OtherReq == [type: {"Timeout", "WriteCompleted", "Sync"}, entry: Entry]

Request == WriteReq \union OtherReq

NullRequest == Request \union {nil}

TypeOK ==
    /\ status \in [Entry -> Status]
    /\ replica_status \in [Entry -> ReplicaStatus]
    /\ dir_state \in [Entry -> DirState]
    /\ pc \in [Node -> PC]
    /\ local_req \in [Node -> NullRequest]
    /\ request_queue \in [Entry -> Seq(Request)]
    /\ num_action \in 0..max_action

-------------------------------------------------------

init_dir_state == [
    status |-> "None", writer |-> {}
]

Init ==
    /\ status = [e \in Entry |-> "None"]
    /\ replica_status = [e \in Entry |-> "Empty"]
    /\ dir_state = [e \in Entry |-> init_dir_state]
    /\ pc = [n \in Node |-> "Init"]
    /\ local_req = [n \in Node |-> nil]
    /\ request_queue = [e \in Entry |-> <<>>]
    /\ num_action = 0

-------------------------------------------------------

input_unchanged ==
    /\ UNCHANGED <<dir_state, replica_status>>
    /\ UNCHANGED <<pc, local_req>>

InsertEntry(e) ==
    /\ status[e] = "None"
    /\ status' = [status EXCEPT ![e] = "CreatingEntry"]

    /\ UNCHANGED num_action
    /\ UNCHANGED request_queue
    /\ input_unchanged

status_existed(e) == status[e] # "None"

AddWriteReq(e, u) ==
    LET
        new_req == [
            type |-> "Write",
            entry |-> e,
            user |-> u
        ]
    IN
    /\ num_action < max_action
    /\ num_action' = num_action + 1
    /\ status_existed(e)

    /\ request_queue' = [request_queue EXCEPT ![e] = Append(@, new_req)]

    /\ UNCHANGED status
    /\ input_unchanged


AddWriteCompleted(e, u) ==
    LET
        new_req == [
            type |-> "WriteCompleted",
            entry |-> e
        ]
    IN
    /\ num_action < max_action
    /\ num_action' = num_action + 1
    /\ status_existed(e)

    /\ request_queue' = [request_queue EXCEPT ![e] = Append(@, new_req)]

    /\ UNCHANGED status
    /\ input_unchanged


-------------------------------------------------------

goto(n, l) ==
    pc' = [pc EXCEPT ![n] = l]

running_nodes == {n \in Node: pc[n] # "Init"}

running_set == {local_req[n].entry: n \in running_nodes}


request_contain(e, n, type) ==
    LET
        req == request_queue[e][1]
    IN
    /\ request_queue[e] # <<>>
    /\ req.type = type
    /\ pc[n] = "Init"
    /\ e \notin running_set
    /\ request_queue' = [request_queue EXCEPT ![e] = Tail(@)]


HandleWriteReq(e, n) ==
    LET
        req == request_queue[e][1]

        when_creating_entry ==
            /\ status[e] = "CreatingEntry"
            /\ goto(n, "CreateDir")
            /\ local_req' = [local_req EXCEPT ![n] = req]

        when_other ==
            /\ status[e] # "CreatingEntry"
            /\ goto(n, "AddWritePerm")
            /\ local_req' = [local_req EXCEPT ![n] = req]
    IN
    /\ request_contain(e, n, "Write")

    /\ \/ when_creating_entry
       \/ when_other

    /\ UNCHANGED <<dir_state, replica_status>>
    /\ UNCHANGED num_action
    /\ UNCHANGED status


CreateDir(n) ==
    LET
        e == local_req[n].entry
    IN
    /\ pc[n] = "CreateDir"
    /\ goto(n, "AddWritePerm")

    /\ dir_state' = [dir_state EXCEPT ![e].status = "Created"]

    /\ UNCHANGED status
    /\ UNCHANGED local_req
    /\ UNCHANGED num_action
    /\ UNCHANGED request_queue
    /\ UNCHANGED replica_status


AddWritePerm(n) ==
    LET
        req == local_req[n]
        e == req.entry
    IN
    /\ pc[n] = "AddWritePerm"
    /\ goto(n, "UpdateReplicaToWriting")

    /\ dir_state' = [dir_state EXCEPT ![e].writer = @ \union {req.user}]

    /\ UNCHANGED local_req
    /\ UNCHANGED status
    /\ UNCHANGED request_queue
    /\ UNCHANGED replica_status
    /\ UNCHANGED num_action


UpdateReplicaToWriting(n) ==
    LET
        req == local_req[n]
        e == req.entry

        update_if_not_written(old) ==
            IF old = "Written"
                THEN old
                ELSE "Writing"
    IN
    /\ pc[n] = "UpdateReplicaToWriting"
    /\ goto(n, "UpdateStatusToWriting")

    /\ replica_status' = [replica_status EXCEPT ![e] = update_if_not_written(@)]

    /\ UNCHANGED dir_state
    /\ UNCHANGED local_req
    /\ UNCHANGED status
    /\ UNCHANGED request_queue
    /\ UNCHANGED num_action


UpdateStatusToWriting(n) ==
    LET
        req == local_req[n]
        e == req.entry
    IN
    /\ pc[n] = "UpdateStatusToWriting"
    /\ goto(n, "Init")

    /\ status' = [status EXCEPT ![e] = "Writing"]
    /\ local_req' = [local_req EXCEPT ![n] = nil]

    /\ UNCHANGED dir_state
    /\ UNCHANGED num_action
    /\ UNCHANGED request_queue
    /\ UNCHANGED replica_status


HandleTimeout(e, n) ==
    LET
        req == request_queue[e][1]

        when_writing ==
            /\ status[e] = "Writing"
            /\ goto(n, "UpdateToWriteTimeout")
            /\ local_req' = [local_req EXCEPT ![n] = req]

        when_write_timeout ==
            /\ status[e] \in {"WriteTimeout", "WriteCompleted"}
            /\ goto(n, "SyncToWritten")
            /\ local_req' = [local_req EXCEPT ![n] = req]

        when_other ==
            /\ status[e] \notin {"Writing", "WriteTimeout", "WriteCompleted"}
            /\ goto(n, "Init")
            /\ UNCHANGED local_req
    IN
    /\ request_contain(e, n, "Timeout")

    /\ \/ when_writing
       \/ when_write_timeout
       \/ when_other

    /\ UNCHANGED num_action
    /\ UNCHANGED <<dir_state, replica_status>>
    /\ UNCHANGED status


UpdateToWriteTimeout(n) ==
    LET
        req == local_req[n]
        e == req.entry

        new_req == [
            type |-> "Sync",
            entry |-> e
        ]
    IN
    /\ pc[n] = "UpdateToWriteTimeout"
    /\ goto(n, "Init")

    /\ status' = [status EXCEPT ![e] = "WriteTimeout"]
    /\ local_req' = [local_req EXCEPT ![n] = nil]
    /\ request_queue' = [request_queue EXCEPT
            ![e] = Append(@, new_req)
        ]

    /\ UNCHANGED num_action
    /\ UNCHANGED <<dir_state, replica_status>>


SyncToWritten(n) ==
    LET
        req == local_req[n]
        e == req.entry
    IN
    /\ pc[n] = "SyncToWritten"
    /\ goto(n, "UpdateToSynced")

    /\ replica_status' = [replica_status EXCEPT ![e] = "Written"]

    /\ UNCHANGED status
    /\ UNCHANGED local_req
    /\ UNCHANGED num_action
    /\ UNCHANGED request_queue
    /\ UNCHANGED dir_state


UpdateToSynced(n) ==
    LET
        req == local_req[n]
        e == req.entry
    IN
    /\ pc[n] = "UpdateToSynced"
    /\ goto(n, "Init")

    /\ status' = [status EXCEPT ![e] = "Synced"]
    /\ local_req' = [local_req EXCEPT ![n] = nil]

    /\ UNCHANGED <<dir_state, replica_status>>
    /\ UNCHANGED num_action
    /\ UNCHANGED request_queue


HandleSyncReq(e, n) ==
    LET
        req == request_queue[e][1]

        valid_status == {"WriteTimeout", "WriteCompleted"}

        when_valid ==
            /\ status[e] \in valid_status
            /\ goto(n, "SyncToWritten")
            /\ local_req' = [local_req EXCEPT ![n] = req]

        when_invalid_status ==
            /\ status[e] \notin valid_status
            /\ goto(n, "Init")
            /\ UNCHANGED local_req
    IN
    /\ request_contain(e, n, "Sync")

    /\ \/ when_valid
       \/ when_invalid_status

    /\ UNCHANGED num_action
    /\ UNCHANGED <<dir_state, replica_status>>
    /\ UNCHANGED status


HandleWriteCompletedReq(e, n) ==
    LET
        req == request_queue[e][1]

        when_writing ==
            /\ status[e] = "Writing"
            /\ goto(n, "UpdateToWriteCompleted")
            /\ local_req' = [local_req EXCEPT ![n] = req]

        when_other ==
            /\ status[e] # "Writing"
            /\ goto(n, "Init")
            /\ UNCHANGED local_req
    IN
    /\ request_contain(e, n, "WriteCompleted")

    /\ \/ when_writing
       \/ when_other

    /\ UNCHANGED <<dir_state, replica_status>>
    /\ UNCHANGED num_action
    /\ UNCHANGED status


UpdateToWriteCompleted(n) ==
    LET
        req == local_req[n]
        e == req.entry

        new_req == [
            type |-> "Sync",
            entry |-> e
        ]
    IN
    /\ pc[n] = "UpdateToWriteCompleted"
    /\ goto(n, "Init")

    /\ status' = [status EXCEPT ![e] = "WriteCompleted"]
    /\ local_req' = [local_req EXCEPT ![n] = nil]
    /\ request_queue' = [request_queue EXCEPT
            ![e] = Append(@, new_req)
        ]

    /\ UNCHANGED num_action
    /\ UNCHANGED <<dir_state, replica_status>>

-------------------------------------------------------

Range(f) == {f[x]: x \in DOMAIN f}

WriteTimeout(e, n) ==
    LET
        new_req == [
            type |-> "Timeout",
            entry |-> e
        ]

        all_reqs == Range(request_queue[e])

        timeout_reqs == {req \in all_reqs: req.type = "Timeout"}

        num_timeout == Cardinality(timeout_reqs)
    IN
    /\ status[e] \in {"Writing", "WriteTimeout"}
    /\ num_timeout < max_timeout

    /\ request_queue' = [request_queue EXCEPT
            ![e] = Append(@, new_req)
        ]

    /\ UNCHANGED status
    /\ UNCHANGED <<pc, local_req>>
    /\ UNCHANGED <<dir_state, replica_status>>
    /\ UNCHANGED num_action

-------------------------------------------------------

StopCond ==
    /\ \A e \in Entry:
        /\ request_queue[e] = <<>>
        /\ status[e] \in {"CreatingEntry", "Synced", "SyncFailed"}

TerminateCond ==
    /\ StopCond
    /\ num_action = max_action

Terminated ==
    /\ TerminateCond
    /\ UNCHANGED vars

Next ==
    \/ \E e \in Entry:
        \/ InsertEntry(e)

    \/ \E e \in Entry, u \in User:
        \/ AddWriteReq(e, u)
        \/ AddWriteCompleted(e, u)

    \/ \E n \in Node:
        \/ CreateDir(n)
        \/ AddWritePerm(n)
        \/ UpdateReplicaToWriting(n)
        \/ UpdateStatusToWriting(n)
        \/ UpdateToWriteTimeout(n)
        \/ UpdateToWriteCompleted(n)
        \/ SyncToWritten(n)
        \/ UpdateToSynced(n)

    \/ \E n \in Node, e \in Entry:
        \/ HandleWriteReq(e, n)
        \/ HandleTimeout(e, n)
        \/ WriteTimeout(e, n)
        \/ HandleSyncReq(e, n)
        \/ HandleWriteCompletedReq(e, n)

    \/ Terminated

Spec == Init /\ [][Next]_vars

FairSpec == Spec /\ WF_vars(Next)

-------------------------------------------------------

AlwaysTerminate == <> TerminateCond

statusTransitionStep ==
    \E e \in Entry:
        \/ /\ status[e] = "None"
           /\ status'[e] = "CreatingEntry"

        \/ /\ status[e] = "CreatingEntry"
           /\ status'[e] = "Writing"

        \/ /\ status[e] = "Writing"
           /\ status'[e] = "WriteTimeout"

        \/ /\ status[e] = "Writing"
           /\ status'[e] = "WriteCompleted"

        \/ /\ status[e] = "WriteTimeout"
           /\ status'[e] = "Synced"

        \/ /\ status[e] = "WriteCompleted"
           /\ status'[e] = "Synced"

        \/ /\ status[e] = "WriteTimeout"
           /\ status'[e] = "Writing"

        \/ /\ status[e] = "WriteCompleted"
           /\ status'[e] = "Writing"

        \/ /\ status[e] = "Synced"
           /\ status'[e] = "Writing"

StatusTransitionInv ==
    [][statusTransitionStep]_status


CanNotHandleEntryConcurrently ==
    Cardinality(running_set) = Cardinality(running_nodes)


MustNotCreateDirWhenNonCreatingEntry ==
    \A n \in Node:
        pc[n] = "CreateDir" => status[local_req[n].entry] = "CreatingEntry"


PCInitInv ==
    \A n \in Node:
        pc[n] = "Init" =>
            /\ local_req[n] = nil


StopCondReplicaStatusMustBeWritten ==
    LET
        cond ==
            \A e \in Entry:
                status[e] # "CreatingEntry" => replica_status[e] = "Written"
    IN
        StopCond => cond

====

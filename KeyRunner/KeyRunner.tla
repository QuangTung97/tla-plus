------ MODULE KeyRunner ----
EXTENDS TLC, Naturals, Sequences, FiniteSets

CONSTANTS Key, nil

VARIABLES keys, running, thread, num_update

vars == <<keys, running, thread, num_update>>

State == {"Start", "WaitOnCancel", "Finished"}

max_update == 5

ThreadInfo == [pc: State, key: Key, cancelled: BOOLEAN]

Thread == 1..max_update

TypeOK ==
    /\ keys \subseteq Key
    /\ running \in [Key -> Thread \union {nil}]
    /\ thread \in Seq(ThreadInfo)
    /\ num_update \in 0..max_update
    /\ DOMAIN thread \subseteq Thread


Init ==
    /\ keys = {}
    /\ running = [k \in Key |-> nil]
    /\ thread = <<>>
    /\ num_update = 0


AddKey(k) ==
    LET
        new_thread == [
            pc |-> "Start",
            key |-> k,
            cancelled |-> FALSE
        ]

        start_new ==
            /\ thread' = Append(thread, new_thread)
            /\ running' = [running EXCEPT ![k] = Len(thread')]

        hold_back ==
            /\ UNCHANGED running
            /\ UNCHANGED thread

        start_new_thread_or_hold_back ==
            IF running[k] = nil
                THEN start_new
                ELSE hold_back
    IN
        /\ ~(k \in keys)
        /\ num_update < max_update
        /\ num_update' = num_update + 1
        /\ keys' = keys \union {k}
        /\ start_new_thread_or_hold_back


RemoveKey(k) ==
    /\ k \in keys
    /\ num_update < max_update
    /\ num_update' = num_update + 1
    /\ keys' = keys \ {k}
    /\ thread' = [thread EXCEPT ![running[k]].cancelled = TRUE]
    /\ UNCHANGED running


StartRunning(th) ==
    /\ th \in DOMAIN thread
    /\ thread[th].pc = "Start"
    /\ thread' = [thread EXCEPT ![th].pc = "WaitOnCancel"]
    /\ UNCHANGED running
    /\ UNCHANGED <<num_update, keys>>


ThreadFinish(th) ==
    LET
        k == thread[th].key

        restart ==
            /\ UNCHANGED running
            /\ thread' = [thread EXCEPT
                    ![th].pc = "Start",
                    ![th].cancelled = FALSE
                ]

        finish ==
            /\ thread' = [thread EXCEPT ![th].pc = "Finished"]
            /\ running' = [running EXCEPT ![k] = nil]

        restart_or_finish ==
            IF k \in keys
                THEN restart
                ELSE finish
    IN
    /\ th \in DOMAIN thread
    /\ thread[th].pc = "WaitOnCancel"
    /\ thread[th].cancelled
    /\ restart_or_finish
    /\ UNCHANGED <<keys, num_update>>


threadBlockedCond ==
    /\ \A th \in DOMAIN thread:
        \/ /\ thread[th].pc = "WaitOnCancel"
           /\ thread[th].cancelled = FALSE
        \/ thread[th].pc = "Finished"


TerminateCond ==
    /\ threadBlockedCond
    /\ num_update = max_update


Terminated ==
    /\ TerminateCond
    /\ UNCHANGED vars


Next ==
    \/ \E k \in Key:
        \/ AddKey(k)
        \/ RemoveKey(k)
    \/ \E th \in 1..max_update:
        \/ StartRunning(th)
        \/ ThreadFinish(th)
    \/ Terminated

Spec == Init /\ [][Next]_vars

FairSpec == Spec /\ WF_vars(Next)


running_thread == {th \in DOMAIN thread: thread[th].pc = "WaitOnCancel"}

NumRunningThreadShouldMatchKeys ==
    LET
        running_keys == {thread[th].key: th \in running_thread}
    IN
        threadBlockedCond => running_keys = keys


NotAllowConcurrentRunning ==
    LET
        threads_by_key(k) == {th \in running_thread: thread[th].key = k}
    IN
        \A k \in Key: Cardinality(threads_by_key(k)) <= 1


AlwaysTerminate == <> TerminateCond

====

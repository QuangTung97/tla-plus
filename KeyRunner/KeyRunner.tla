------ MODULE KeyRunner ----
EXTENDS TLC, Naturals, Sequences, FiniteSets

CONSTANTS Key, nil

VARIABLES keys, running, thread, num_update, value, next_val

vars == <<keys, running, thread, num_update, value, next_val>>

State == {"Start", "WaitOnCancel", "Finished"}

max_update == 6

Value == 30..40

ThreadInfo == [pc: State, key: Key, val: Value, cancelled: BOOLEAN]

Thread == 1..max_update


TypeOK ==
    /\ keys \subseteq Key
    /\ running \in [Key -> Thread \union {nil}]
    /\ thread \in Seq(ThreadInfo)
    /\ num_update \in 0..max_update
    /\ DOMAIN thread \subseteq Thread
    /\ value \in [Key -> Value]
    /\ next_val \in Value


Init ==
    /\ keys = {}
    /\ running = [k \in Key |-> nil]
    /\ thread = <<>>
    /\ num_update = 0
    /\ value = [k \in Key |-> 30]
    /\ next_val = 30


AddKey(k) ==
    LET
        new_thread == [
            pc |-> "Start",
            key |-> k,
            val |-> value'[k],
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
        /\ next_val' = next_val + 1
        /\ value' = [value EXCEPT ![k] = next_val']
        /\ start_new_thread_or_hold_back


RemoveKey(k) ==
    /\ k \in keys
    /\ num_update < max_update
    /\ num_update' = num_update + 1
    /\ keys' = keys \ {k}
    /\ thread' = [thread EXCEPT ![running[k]].cancelled = TRUE]
    /\ value' = [value EXCEPT ![k] = 30]
    /\ UNCHANGED next_val
    /\ UNCHANGED running


UpdateKey(k) ==
    /\ k \in keys
    /\ num_update < max_update
    /\ num_update' = num_update + 1
    /\ next_val' = next_val + 1
    /\ value' = [value EXCEPT ![k] = next_val']
    /\ thread' = [thread EXCEPT ![running[k]].cancelled = TRUE]
    /\ UNCHANGED <<keys, running>>


StartRunning(th) ==
    /\ th \in DOMAIN thread
    /\ thread[th].pc = "Start"
    /\ thread' = [thread EXCEPT ![th].pc = "WaitOnCancel"]
    /\ UNCHANGED <<value, next_val>>
    /\ UNCHANGED running
    /\ UNCHANGED <<num_update, keys>>


ThreadFinish(th) ==
    LET
        k == thread[th].key

        restart ==
            /\ UNCHANGED running
            /\ thread' = [thread EXCEPT
                    ![th].pc = "Start",
                    ![th].val = value[k],
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
    /\ UNCHANGED <<value, next_val>>
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
        \/ UpdateKey(k)
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

        value_matched ==
            \A th \in running_thread:
                thread[th].val = value[thread[th].key]
    IN
        threadBlockedCond =>
            /\ running_keys = keys
            /\ value_matched


NotAllowConcurrentRunning ==
    LET
        threads_by_key(k) == {th \in running_thread: thread[th].key = k}
    IN
        \A k \in Key: Cardinality(threads_by_key(k)) <= 1


RunningStateMatchThreadState ==
    LET
        existed_thread(k) ==
            \E th \in DOMAIN thread:
                /\ thread[th].key = k
                /\ \/ thread[th].pc = "WaitOnCancel"
                   \/ thread[th].pc = "Start"
    IN
    \A k \in Key:
        running[k] # nil <=> existed_thread(k)


KeysAlwaysImplyRunning ==
    \A k \in keys: running[k] # nil


ValueMatchKeys ==
    \A k \in Key:
        value[k] > 30 <=> k \in keys


AlwaysTerminate == <> TerminateCond

====

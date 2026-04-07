---- MODULE CancelWorker ----
EXTENDS TLC, Naturals, FiniteSets

CONSTANTS Node, nil

VARIABLES
    pc, last_action, local_action,
    running_set, current_step, enable_timer

vars == <<
    pc, last_action, local_action,
    running_set, current_step, enable_timer
>>

-----------------------------------------------------------------------

ActionID == 20..29
NullAction == ActionID \union {nil}

PC == {"Init", "LockRunner", "RunWorkerTask", "ExecuteLongAction", "Terminated"}

Step == {"BeginTask", "LongAction"}
NullStep == Step \union {nil}

-----------------------------------------------------------------------

TypeOK ==
    /\ pc \in [Node -> PC]
    /\ last_action \in ActionID
    /\ local_action \in [Node -> NullAction]
    /\ running_set \subseteq ActionID
    /\ current_step \in NullStep
    /\ enable_timer \in BOOLEAN

Init ==
    /\ pc = [n \in Node |-> "Init"]
    /\ last_action = 20
    /\ local_action = [n \in Node |-> nil]
    /\ running_set = {}
    /\ current_step = nil
    /\ enable_timer = FALSE

-----------------------------------------------------------------------

goto(n, l) ==
    pc' = [pc EXCEPT ![n] = l]

should_enable_timer ==
    Cardinality(running_set') > 1 /\ current_step' = "LongAction"

do_enable_timer ==
    IF should_enable_timer
        THEN enable_timer' = TRUE
        ELSE UNCHANGED enable_timer

StartWorker(n) ==
    /\ pc[n] = "Init"
    /\ goto(n, "LockRunner")
    /\ last_action' = last_action + 1
    /\ running_set' = running_set \union {last_action'}
    /\ local_action' = [local_action EXCEPT ![n] = last_action']
    /\ UNCHANGED current_step
    /\ do_enable_timer


LockRunner(n) ==
    /\ pc[n] = "LockRunner"
    /\ current_step = nil
    /\ current_step' = "BeginTask"
    /\ goto(n, "RunWorkerTask")
    /\ UNCHANGED enable_timer
    /\ UNCHANGED last_action
    /\ UNCHANGED local_action
    /\ UNCHANGED running_set


RunWorkerTask(n) ==
    /\ pc[n] = "RunWorkerTask"
    /\ goto(n, "ExecuteLongAction")

    /\ current_step' = "LongAction"
    /\ UNCHANGED running_set
    /\ do_enable_timer

    /\ UNCHANGED local_action
    /\ UNCHANGED last_action


ExecuteLongAction(n) ==
    /\ pc[n] = "ExecuteLongAction"
    /\ goto(n, "Terminated")
    /\ current_step' = nil
    /\ running_set' = running_set \ {local_action[n]}
    /\ IF ~should_enable_timer
        THEN enable_timer' = FALSE
        ELSE UNCHANGED enable_timer
    /\ UNCHANGED local_action
    /\ UNCHANGED last_action

-----------------------------------------------------------------------

TerminateCond ==
    /\ \A n \in Node: pc[n] = "Terminated"

Terminated ==
    /\ TerminateCond
    /\ UNCHANGED vars


Next ==
    \/ \E n \in Node:
        \/ StartWorker(n)
        \/ LockRunner(n)
        \/ RunWorkerTask(n)
        \/ ExecuteLongAction(n)
    \/ Terminated

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------

TerminatedInv ==
    TerminateCond =>
        /\ current_step = nil
        /\ enable_timer = FALSE


EnableTimerInv ==
    LET
        cond ==
            /\ Cardinality(running_set) > 1
            /\ current_step = "LongAction"
    IN
    enable_timer <=> cond

====

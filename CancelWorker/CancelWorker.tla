---- MODULE CancelWorker ----
EXTENDS TLC, Naturals, FiniteSets

CONSTANTS Node, nil

VARIABLES
    pc, last_action, local_action,
    running_map, current_step,
    current_action, enable_timer

vars == <<
    pc, last_action, local_action,
    running_map, current_step,
    current_action, enable_timer
>>

-----------------------------------------------------------------------

num_nodes == Cardinality(Node)

ActionID == 20..(20 + num_nodes)
NullAction == ActionID \union {nil}

PC == {"Init", "LockRunner", "RunWorkerTask", "ExecuteLongAction", "Terminated"}

Step == {"BeginTask", "LongAction"}
NullStep == Step \union {nil}

ActionType == {"Foreground", "Background"}
NullType == ActionType \union {nil}

-----------------------------------------------------------------------

TypeOK ==
    /\ pc \in [Node -> PC]
    /\ last_action \in ActionID
    /\ local_action \in [Node -> NullAction]
    /\ running_map \in [ActionID -> NullType]
    /\ current_step \in NullStep
    /\ current_action \in NullAction
    /\ enable_timer \in BOOLEAN

Init ==
    /\ pc = [n \in Node |-> "Init"]
    /\ last_action = 20
    /\ local_action = [n \in Node |-> nil]
    /\ running_map = [a \in ActionID |-> nil]
    /\ current_step = nil
    /\ current_action = nil
    /\ enable_timer = FALSE

-----------------------------------------------------------------------

goto(n, l) ==
    pc' = [pc EXCEPT ![n] = l]


foreground_set(input_map) ==
    {a \in ActionID: input_map[a] # nil /\ input_map[a] = "Foreground"}

should_enable_timer ==
    LET
        other_running == foreground_set(running_map') \ {current_action'}
    IN
        /\ Cardinality(other_running) > 0
        /\ current_step' = "LongAction"

do_enable_timer ==
    IF should_enable_timer
        THEN enable_timer' = TRUE
        ELSE UNCHANGED enable_timer

StartWorker(n, action_type) ==
    /\ pc[n] = "Init"
    /\ goto(n, "LockRunner")
    /\ last_action' = last_action + 1
    /\ running_map' = [running_map EXCEPT ![last_action'] = action_type]
    /\ local_action' = [local_action EXCEPT ![n] = last_action']
    /\ UNCHANGED current_step
    /\ UNCHANGED current_action
    /\ do_enable_timer


LockRunner(n) ==
    /\ pc[n] = "LockRunner"
    /\ current_step = nil
    /\ current_step' = "BeginTask"
    /\ UNCHANGED current_action
    /\ goto(n, "RunWorkerTask")
    /\ UNCHANGED enable_timer
    /\ UNCHANGED last_action
    /\ UNCHANGED local_action
    /\ UNCHANGED running_map


RunWorkerTask(n) ==
    /\ pc[n] = "RunWorkerTask"
    /\ goto(n, "ExecuteLongAction")

    /\ current_step' = "LongAction"
    /\ current_action' = local_action[n]
    /\ UNCHANGED running_map
    /\ do_enable_timer

    /\ UNCHANGED local_action
    /\ UNCHANGED last_action


ExecuteLongAction(n) ==
    LET
        a == local_action[n]
    IN
    /\ pc[n] = "ExecuteLongAction"
    /\ goto(n, "Terminated")
    /\ current_step' = nil
    /\ running_map' = [running_map EXCEPT ![a] = nil]
    /\ current_action' = nil
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
        \/ \E action_type \in ActionType: StartWorker(n, action_type)
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
        other_running == foreground_set(running_map) \ {current_action}
        cond ==
            /\ Cardinality(other_running) > 0
            /\ current_step = "LongAction"
    IN
        enable_timer <=> cond

====

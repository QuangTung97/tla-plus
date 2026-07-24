---- MODULE CancelSvcV2 ----
EXTENDS TLC, FiniteSets, Naturals

CONSTANTS Node, Key, nil

VARIABLES
    last_action_id, running_map, enabled_timer,
    locked_set,
    pc, local_action_id, local_key

local_vars == <<
    pc, local_action_id, local_key
>>

vars == <<
    last_action_id, running_map, enabled_timer,
    locked_set,
    local_vars
>>

-----------------------------------------------------------

Null(S) == S \union {nil}

ActionID == 21..(20 + Cardinality(Node))

ZeroActionID == ActionID \union {20}

ActionType == {"Foreground", "Background"}

RunningInfo == [
    canceled: BOOLEAN
]

ActionState == [
    action_type: ActionType,
    running: Null(RunningInfo)
]

RunningState == [
    active_actions: [ActionID -> Null(ActionState)]
]

PC == {
    "Init",
    "LockKey", "Running", "StopRunning", "UnlockKey",
    "Finish", "Terminated"
}

-----------------------------------------------------------

TypeOK ==
    /\ last_action_id \in ZeroActionID
    /\ running_map \in [Key -> Null(RunningState)]
    /\ enabled_timer \subseteq Key
    /\ locked_set \subseteq Key

    /\ pc \in [Node -> PC]
    /\ local_action_id \in [Node -> Null(ActionID)]
    /\ local_key \in [Node -> Null(Key)]

Init ==
    /\ last_action_id = 20
    /\ running_map = [k \in Key |-> nil]
    /\ enabled_timer = {}
    /\ locked_set = {}

    /\ pc = [n \in Node |-> "Init"]
    /\ local_action_id = [n \in Node |-> nil]
    /\ local_key = [n \in Node |-> nil]

-----------------------------------------------------------

set_local(n, var, x) ==
    var' = [var EXCEPT ![n] = x]

goto(n, l) ==
    pc' = [pc EXCEPT ![n] = l]

-----------------------------------------------------------

need_enable_timer(state) ==
    LET
        get_action_state(id) ==
            state.active_actions[id]

        is_foreground(action_state) ==
            /\ action_state # nil
            /\ action_state.action_type = "Foreground"

        is_running(action_state) ==
            /\ action_state # nil
            /\ action_state.running # nil

        foreground_set ==
            {id \in ActionID: is_foreground(get_action_state(id))}

        running_set ==
            {id \in ActionID: is_running(get_action_state(id))}
    IN
        /\ state # nil
        /\ running_set # {}
        /\ foreground_set # {}
        /\ foreground_set \ running_set # {}

-----------------------------------------------------------

update_enabled_timer(input_running_map, k) ==
    IF need_enable_timer(input_running_map[k]) THEN
        enabled_timer' = enabled_timer \union {k}
    ELSE
        enabled_timer' = enabled_timer \ {k}

-----------------------------------------------------------

NewSession(n, k, action_type) ==
    LET
        id == last_action_id + 1

        new_action_state == [
            action_type |-> action_type,
            running |-> nil
        ]

        old_action_state_map ==
            IF running_map[k] # nil
                THEN running_map[k].active_actions
                ELSE [a \in ActionID |-> nil]

        new_action_state_map == [
            old_action_state_map EXCEPT ![id] = new_action_state
        ]

        new_state == [
            active_actions |-> new_action_state_map
        ]
    IN
    /\ pc[n] = "Init"

    /\ goto(n, "LockKey")
    /\ last_action_id' = id
    /\ running_map' = [running_map EXCEPT ![k] = new_state]

    /\ set_local(n, local_action_id, id)
    /\ set_local(n, local_key, k)

    /\ update_enabled_timer(running_map', k)

    /\ UNCHANGED locked_set

-----------------------------------------------------------

do_lock_key(k) ==
    /\ k \notin locked_set
    /\ locked_set' = locked_set \union {k}

------------------------------

LockKey(n) ==
    LET
        k == local_key[n]

        on_normal ==
            /\ goto(n, "Running")
            /\ do_lock_key(k)

        on_failed ==
            /\ goto(n, "Finish")
            /\ UNCHANGED locked_set
    IN
    /\ pc[n] = "LockKey"
    /\ \/ on_normal
       \/ on_failed
    /\ UNCHANGED running_map
    /\ UNCHANGED <<local_action_id, local_key>>
    /\ UNCHANGED enabled_timer
    /\ UNCHANGED last_action_id

-----------------------------------------------------------

RunAction(n) ==
    LET
        k == local_key[n]
        id == local_action_id[n]

        new_running == [
            canceled |-> FALSE
        ]
    IN
    /\ pc[n] = "Running"

    /\ goto(n, "StopRunning")
    /\ running_map' = [running_map EXCEPT
            ![k].active_actions[id].running = new_running]
    /\ update_enabled_timer(running_map', k)

    /\ UNCHANGED last_action_id
    /\ UNCHANGED locked_set
    /\ UNCHANGED <<local_action_id, local_key>>

-----------------------------------------------------------

StopRunning(n) ==
    LET
        k == local_key[n]
        id == local_action_id[n]
    IN
    /\ pc[n]= "StopRunning"
    /\ goto(n, "UnlockKey")

    /\ running_map' = [running_map EXCEPT
            ![k].active_actions[id].running = nil]
    /\ update_enabled_timer(running_map', k)

    /\ UNCHANGED last_action_id
    /\ UNCHANGED locked_set
    /\ UNCHANGED <<local_action_id, local_key>>

-----------------------------------------------------------

UnlockKey(n) ==
    LET
        k == local_key[n]
    IN
    /\ pc[n] = "UnlockKey"

    /\ goto(n, "Finish")
    /\ locked_set' = locked_set \ {k}

    /\ UNCHANGED running_map
    /\ UNCHANGED enabled_timer
    /\ UNCHANGED last_action_id
    /\ UNCHANGED <<local_action_id, local_key>>

-----------------------------------------------------------

FinishNode(n) ==
    LET
        k == local_key[n]
        id == local_action_id[n]

        old_action_map == running_map[k].active_actions

        new_action_map == [old_action_map EXCEPT ![id] = nil]

        non_empty_id == {x \in ActionID: new_action_map[x] # nil}

        new_state ==
            IF non_empty_id = {}
                THEN nil
                ELSE [active_actions |-> new_action_map]
    IN
    /\ pc[n] = "Finish"
    /\ goto(n, "Terminated")

    /\ running_map' = [running_map EXCEPT ![k] = new_state]
    /\ update_enabled_timer(running_map', k)

    /\ UNCHANGED locked_set
    /\ UNCHANGED last_action_id
    /\ UNCHANGED <<local_action_id, local_key>>

-----------------------------------------------------------

TerminateCond ==
    /\ \A n \in Node: pc[n] = "Terminated"

Terminated ==
    /\ TerminateCond
    /\ UNCHANGED vars

-----------------------------------------------------------

Next ==
    \/ \E n \in Node, k \in Key, t \in ActionType:
        \/ NewSession(n, k, t)
    \/ \E n \in Node:
        \/ LockKey(n)
        \/ RunAction(n)
        \/ StopRunning(n)
        \/ UnlockKey(n)
        \/ FinishNode(n)
    \/ Terminated

Spec == Init /\ [][Next]_vars

FairSpec == Spec /\ WF_vars(Next)

-----------------------------------------------------------

AlwaysTerminated == []<>TerminateCond


RunningMapInv ==
    LET
        cond(k, id) ==
            /\ running_map[k] # nil
            /\ running_map[k].active_actions[id] # nil
    IN
    \A n \in Node:
        pc[n] \notin {"Init", "Terminated"} =>
            cond(local_key[n], local_action_id[n])


EnabledTimerMatchRunningMap ==
    \A k \in Key: k \in enabled_timer <=> need_enable_timer(running_map[k])


WhenTerminatedInv ==
    TerminateCond =>
        /\ \A k \in Key: running_map[k] = nil
        /\ enabled_timer = {}
        /\ locked_set = {}

====

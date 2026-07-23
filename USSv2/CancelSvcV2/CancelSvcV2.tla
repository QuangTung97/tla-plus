---- MODULE CancelSvcV2 ----
EXTENDS TLC, FiniteSets, Naturals

CONSTANTS Node, Key, nil

VARIABLES
    last_action_id, running_map, enabled_timer,
    pc, local_action_id, local_key

local_vars == <<
    pc, local_action_id, local_key
>>

vars == <<
    last_action_id, running_map, enabled_timer,
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

PC == {"Init", "LockKey", "Terminated"}

-----------------------------------------------------------

TypeOK ==
    /\ last_action_id \in ZeroActionID
    /\ running_map \in [Key -> Null(RunningState)]
    /\ enabled_timer \subseteq Key

    /\ pc \in [Node -> PC]
    /\ local_action_id \in [Node -> Null(ActionID)]
    /\ local_key \in [Node -> Null(Key)]

Init ==
    /\ last_action_id = 20
    /\ running_map = [k \in Key |-> nil]
    /\ enabled_timer = {}

    /\ pc = [n \in Node |-> "Init"]
    /\ local_action_id = [n \in Node |-> nil]
    /\ local_key = [n \in Node |-> nil]

-----------------------------------------------------------

set_local(n, var, x) ==
    var' = [var EXCEPT ![n] = x]

goto(n, l) ==
    pc' = [pc EXCEPT ![n] = l]

-----------------------------------------------------------

NewSession(n, k, action_type) ==
    LET
        id == last_action_id + 1

        new_action_state == [
            action_type |-> action_type,
            running |-> nil
        ]

        old_action_state_map == [a \in ActionID |-> nil]

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

    /\ UNCHANGED enabled_timer \* TODO

-----------------------------------------------------------

TerminateCond ==
    /\ TRUE

Terminated ==
    /\ TerminateCond
    /\ UNCHANGED vars

-----------------------------------------------------------

Next ==
    \/ \E n \in Node, k \in Key, t \in ActionType:
        \/ NewSession(n, k, t)
    \/ Terminated

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------

====

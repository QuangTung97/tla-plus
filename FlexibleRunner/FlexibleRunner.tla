---- MODULE FlexibleRunner ----
EXTENDS TLC, Naturals, Sequences, FiniteSets

CONSTANTS Node, nil, max_action

VARIABLES
    latest_action, action_queue, running_set,
    limit_runner, num_runner,
    pc, local_action

vars == <<
    latest_action, action_queue, running_set,
    limit_runner, num_runner,
    pc, local_action
>>

---------------------------------------------------------

Null(S) == S \union {nil}

Range(f) == {f[x]: x \in DOMAIN f}

---------------------------------------------------------

num_nodes == Cardinality(Node)

max_action_num == 20 + max_action

Action == 20..max_action_num

PC == {"Init", "GetNext", "RunAction"}

---------------------------------------------------------

TypeOK ==
    /\ latest_action \in Action
    /\ action_queue \in Seq(Action)
    /\ running_set \subseteq Action

    /\ limit_runner \in 1..num_nodes
    /\ num_runner \in 0..num_nodes

    /\ pc \in [Node -> PC]
    /\ local_action \in [Node -> Null(Action)]


Init ==
    /\ latest_action = 20
    /\ action_queue = <<>>
    /\ running_set = {}

    /\ limit_runner \in 1..num_nodes
    /\ num_runner = 0

    /\ pc = [n \in Node |-> "Init"]
    /\ local_action = [n \in Node |-> nil]

---------------------------------------------------------

goto(n, l) ==
    pc' = [pc EXCEPT ![n] = l]

start_new_thread(n) ==
    IF num_runner < limit_runner THEN
        /\ pc[n] = "Init"
        /\ goto(n, "GetNext")
        /\ num_runner' = num_runner + 1
    ELSE
        /\ UNCHANGED pc
        /\ UNCHANGED num_runner

---------------------

AddAction ==
    /\ latest_action < max_action_num
    /\ latest_action' = latest_action + 1
    /\ action_queue' = Append(action_queue, latest_action')
    /\ \E n \in Node: start_new_thread(n)

    /\ UNCHANGED limit_runner
    /\ UNCHANGED running_set
    /\ UNCHANGED local_action

\* TODO support remove action from queue

---------------------

set_local(n, var, data) ==
    var' = [var EXCEPT ![n] = data]

GetNext(n) ==
    LET
        x == action_queue[1]
    IN
    /\ pc[n] = "GetNext"
    /\ goto(n, "RunAction")

    /\ action_queue' = Tail(action_queue)
    /\ running_set' = running_set \union {x}
    /\ set_local(n, local_action, x)

    /\ UNCHANGED num_runner
    /\ UNCHANGED latest_action
    /\ UNCHANGED limit_runner

---------------------

RunAction(n) ==
    LET
        x == local_action[n]

        starting_count == num_runner - Cardinality(running_set)

        continue_cond ==
            /\ Len(action_queue) > starting_count
    IN
    /\ pc[n] = "RunAction"
    /\ IF continue_cond THEN
            /\ goto(n, "GetNext")
            /\ UNCHANGED num_runner
        ELSE
            /\ goto(n, "Init")
            /\ num_runner' = num_runner - 1

    /\ running_set' = running_set \ {x}
    /\ set_local(n, local_action, nil)

    /\ UNCHANGED action_queue
    /\ UNCHANGED latest_action
    /\ UNCHANGED limit_runner

---------------------------------------------------------

TerminateCond ==
    /\ latest_action = max_action_num
    /\ action_queue = <<>>
    /\ \A n \in Node: pc[n] = "Init"
    /\ num_runner = 0
    /\ running_set = {}

Terminated ==
    /\ TerminateCond
    /\ UNCHANGED vars


Next ==
    \/ AddAction
    \/ \E n \in Node:
        \/ GetNext(n)
        \/ RunAction(n)
    \/ Terminated

Spec == Init /\ [][Next]_vars

---------------------------------------------------------

ActionQueueDisjointRunningSetInv ==
    Range(action_queue) \intersect running_set = {}


RunningSetAndNumRunnerInv ==
    Cardinality(running_set) <= num_runner

====

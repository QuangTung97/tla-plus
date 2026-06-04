---- MODULE FlexibleRunner ----
EXTENDS TLC, Naturals, Sequences, FiniteSets

CONSTANTS Node, nil, max_action

VARIABLES
    latest_action, action_queue,
    limit_runner, num_running,
    pc

vars == <<
    latest_action, action_queue,
    limit_runner, num_running,
    pc
>>

---------------------------------------------------------

num_nodes == Cardinality(Node)

max_action_num == 20 + max_action

Action == 20..max_action_num

PC == {"Init"}

---------------------------------------------------------

TypeOK ==
    /\ latest_action \in Action
    /\ action_queue \in Seq(Action)
    /\ limit_runner \in 1..num_nodes
    /\ num_running \in 0..num_nodes
    /\ pc \in [Node -> PC]


Init ==
    /\ latest_action = 20
    /\ action_queue = <<>>
    /\ limit_runner \in 1..num_nodes
    /\ num_running = 0
    /\ pc = [n \in Node |-> "Init"]

---------------------------------------------------------

goto(n, l) ==
    pc' = [pc EXCEPT ![n] = l]

start_new_thread(n) ==
    IF num_running < limit_runner THEN
        /\ goto(n, "GetNext")
        /\ num_running' = num_running + 1
    ELSE
        /\ UNCHANGED pc
        /\ UNCHANGED num_running

AddAction ==
    /\ latest_action < max_action_num
    /\ latest_action' = latest_action + 1
    /\ action_queue' = Append(action_queue, latest_action')
    /\ \E n \in Node: start_new_thread(n)
    /\ UNCHANGED limit_runner

---------------------------------------------------------

TerminateCond ==
    /\ latest_action = max_action_num
    /\ action_queue = <<>>
    /\ \A n \in Node: pc[n] = "Init"
    /\ num_running = 0

Terminated ==
    /\ TerminateCond
    /\ UNCHANGED vars


Next ==
    \/ AddAction
    \/ Terminated

Spec == Init /\ [][Next]_vars

---------------------------------------------------------

====

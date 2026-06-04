---- MODULE FlexibleRunner ----
EXTENDS TLC, Naturals, Sequences, FiniteSets

CONSTANTS Node, nil, max_action, max_extra

VARIABLES
    latest_action, action_queue, running_set,
    limit_runner, num_runner,
    pc, local_action,
    num_extra

vars == <<
    latest_action, action_queue, running_set,
    limit_runner, num_runner,
    pc, local_action,
    num_extra
>>

local_vars == <<pc, local_action>>

---------------------------------------------------------

Null(S) == S \union {nil}

Range(f) == {f[x]: x \in DOMAIN f}

RemoveSeq(seq, i) == SubSeq(seq, 1, i-1) \o SubSeq(seq, i+1, Len(seq))

ASSUME RemoveSeq(<<11, 12, 13>>, 2) = <<11, 13>>
ASSUME RemoveSeq(<<11, 12, 13>>, 1) = <<12, 13>>
ASSUME RemoveSeq(<<11, 12, 13>>, 3) = <<11, 12>>

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

    /\ num_extra \in 0..max_extra


Init ==
    /\ latest_action = 20
    /\ action_queue = <<>>
    /\ running_set = {}

    /\ limit_runner \in 1..num_nodes
    /\ num_runner = 0

    /\ pc = [n \in Node |-> "Init"]
    /\ local_action = [n \in Node |-> nil]

    /\ num_extra = 0

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
    /\ UNCHANGED num_extra

---------------------

allow_extra_action ==
    /\ num_extra < max_extra
    /\ num_extra' = num_extra + 1

RemoveAction ==
    /\ allow_extra_action
    /\ Len(action_queue) > 0

    /\ \E i \in DOMAIN action_queue:
        action_queue' = RemoveSeq(action_queue, i)

    /\ UNCHANGED num_runner
    /\ UNCHANGED running_set
    /\ UNCHANGED limit_runner
    /\ UNCHANGED latest_action
    /\ UNCHANGED local_vars

---------------------

set_local(n, var, data) ==
    var' = [var EXCEPT ![n] = data]

GetNext(n) ==
    LET
        when_empty ==
            /\ goto(n, "Init")
            /\ num_runner' = num_runner - 1
            /\ UNCHANGED action_queue
            /\ UNCHANGED running_set
            /\ UNCHANGED local_action

        x == action_queue[1]

        when_normal ==
            /\ goto(n, "RunAction")
            /\ action_queue' = Tail(action_queue)
            /\ running_set' = running_set \union {x}
            /\ set_local(n, local_action, x)
            /\ UNCHANGED num_runner
    IN
    /\ pc[n] = "GetNext"

    /\ IF Len(action_queue) = 0
        THEN when_empty
        ELSE when_normal

    /\ UNCHANGED latest_action
    /\ UNCHANGED limit_runner
    /\ UNCHANGED num_extra

---------------------

RunAction(n) ==
    LET
        x == local_action[n]

        continue_cond ==
            /\ Len(action_queue) + Cardinality(running_set) > num_runner
            /\ num_runner <= limit_runner
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
    /\ UNCHANGED num_extra

---------------------

ChangeLimitRunner ==
    /\ allow_extra_action

    /\ \E l \in 1..num_nodes:
        /\ l # limit_runner
        /\ limit_runner' = l

    /\ UNCHANGED num_runner
    /\ UNCHANGED latest_action
    /\ UNCHANGED <<action_queue, running_set>>
    /\ UNCHANGED <<pc, local_action>>

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
    \/ RemoveAction
    \/ \E n \in Node:
        \/ GetNext(n)
        \/ RunAction(n)
    \/ ChangeLimitRunner
    \/ Terminated

Spec == Init /\ [][Next]_vars

---------------------------------------------------------

ActionQueueDisjointRunningSetInv ==
    Range(action_queue) \intersect running_set = {}


RunningSetAndNumRunnerInv ==
    Cardinality(running_set) <= num_runner


NumRunnerInv ==
    LET
        set == {n \in Node: pc[n] # "Init"}
    IN
    num_runner = Cardinality(set)


limitRunnerStep ==
    LET
        pre_cond(n) ==
            /\ pc[n] # "GetNext"
            /\ pc'[n] = "GetNext"
    IN
    \A n \in Node:
        pre_cond(n) => num_runner <= limit_runner

LimitRunnerProperty ==
    [][limitRunnerStep]_vars

====

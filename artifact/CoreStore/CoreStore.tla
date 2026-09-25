---- MODULE CoreStore ----
EXTENDS TLC, Naturals, Sequences, FiniteSets

CONSTANTS Node, File, nil

VARIABLES
    global_epoch,
    node_epoch, node_isr, node_leader,
    node_leader_log,
    node_acc_epoch, node_acc_log,
    pc, node_expect_isr

global_vars == <<
    global_epoch
>>

node_vars == <<
    node_epoch, node_isr, node_leader,
    node_leader_log,
    pc, node_expect_isr
>>

acc_vars == <<
    node_acc_epoch, node_acc_log
>>

vars == <<
    global_vars,
    node_vars,
    acc_vars
>>

----------------------------------------------------------------------

Null(S) == S \union {nil}

NonEmpty(S) == (SUBSET S) \ {{}}

ASSUME NonEmpty({1, 2}) = {{1}, {2}, {1, 2}}

----------------------------------------------------------------------

Epoch == 10..19

LogEntry ==
    LET
        new_leader ==[
            epoch: Epoch,
            leader: Node,
            isr: NonEmpty(Node)
        ]
    IN
        UNION {new_leader}

PC == {"Init", "StartElection", "Loop"}

----------------------------------------------------------------------

TypeOK ==
    /\ global_epoch \in Epoch

    /\ node_epoch \in [Node -> Epoch]
    /\ node_isr \in [Node -> SUBSET Node]
    /\ node_leader \in [Node -> Null(Node)]
    /\ node_leader_log \in [Node -> Seq(LogEntry)]

    /\ node_acc_epoch \in [Node -> Epoch]
    /\ node_acc_log \in [Node -> Seq(LogEntry)]

    /\ pc \in [Node -> PC]
    /\ node_expect_isr \in [Node -> Null(NonEmpty(Node))]

Init ==
    /\ global_epoch = 10

    /\ node_epoch = [n \in Node |-> 10]
    /\ node_isr = [n \in Node |-> {}]
    /\ node_leader = [n \in Node |-> nil]
    /\ node_leader_log = [n \in Node |-> <<>>]

    /\ node_acc_epoch = [n \in Node |-> 10]
    /\ node_acc_log = [n \in Node |-> <<>>]

    /\ pc = [n \in Node |-> "Init"]
    /\ node_expect_isr = [n \in Node |-> nil]

----------------------------------------------------------------------

goto(n, l) ==
    pc' = [pc EXCEPT ![n] = l]

set_local(n, var, x) ==
    var' = [var EXCEPT ![n] = x]

----------------------------------------------------------------------

NodeBegin(n, isr) ==
    /\ n \in isr
    /\ pc[n] = "Init"

    /\ goto(n, "StartElection")
    /\ set_local(n, node_expect_isr, isr)

    /\ UNCHANGED <<node_epoch, node_isr>>
    /\ UNCHANGED node_leader
    /\ UNCHANGED node_leader_log
    /\ UNCHANGED acc_vars
    /\ UNCHANGED global_epoch

----------------------------------------------------------------------

StartElection(n) ==
    LET
        isr == node_expect_isr[n]

        entry == [
            epoch |-> global_epoch',
            leader |-> n,
            isr |-> isr
        ]
    IN
    /\ pc[n] = "StartElection"

    /\ global_epoch' = global_epoch + 1
    /\ set_local(n, node_epoch, global_epoch')
    /\ set_local(n, node_leader, n)
    /\ set_local(n, node_isr, isr)
    /\ node_leader_log' = [node_leader_log EXCEPT ![n] = Append(@, entry)]

    /\ goto(n, "Loop")
    /\ set_local(n, node_expect_isr, nil)

    /\ UNCHANGED acc_vars


----------------------------------------------------------------------

Terminated ==
    /\ FALSE
    /\ UNCHANGED vars

----------------------------------------------------------------------

Next ==
    \/ \E n \in Node:
        \/ \E isr \in NonEmpty(Node): NodeBegin(n, isr)
        \/ StartElection(n)
    \/ Terminated

Spec == Init /\ [][Next]_vars

----------------------------------------------------------------------

Next2 == Next

====

------ MODULE OnceRunner ----
EXTENDS TLC, FiniteSets, Naturals, Sequences

CONSTANTS Node, nil

VARIABLES
    pc, global_chan, status, running,
    wait_list, local_chan, ctx_cancelled

vars == <<
    pc, global_chan, status, running,
    wait_list, local_chan, ctx_cancelled
>>

-----------------------------------------------------------------------

PC == {"Init", "WaitOnChan", "Running", "Terminated"}

ChannelData == [
    data: Seq({"OK"})
]

Channel == DOMAIN global_chan

NullChannel == Channel \union {nil}

NullNode == Node \union {nil}

-----------------------------------------------------------------------

TypeOK ==
    /\ pc \in [Node -> PC]
    /\ global_chan \in Seq(ChannelData)
    /\ status \in {"NoJob", "Running", "Cancelling"}
    /\ running \in NullNode
    /\ wait_list \in Seq(Channel)
    /\ local_chan \in [Node -> NullChannel]
    /\ ctx_cancelled \subseteq Node


Init ==
    /\ pc = [n \in Node |-> "Init"]
    /\ global_chan = <<>>
    /\ status = "NoJob"
    /\ running = nil
    /\ wait_list = <<>>
    /\ local_chan = [n \in Node |-> nil]
    /\ ctx_cancelled = {}

-----------------------------------------------------------------------

goto(n, l) ==
    pc' = [pc EXCEPT ![n] = l]

empty_chan == [
    data |-> <<>>
]

is_cancelled(n) == n \in ctx_cancelled

StartJob(n) ==
    LET
        when_normal ==
            /\ goto(n, "Running")
            /\ running' = n
            /\ status' = "Running"
            /\ UNCHANGED global_chan
            /\ UNCHANGED local_chan
            /\ UNCHANGED ctx_cancelled
            /\ UNCHANGED wait_list

        new_ch == Len(global_chan')

        when_running ==
            /\ goto(n, "WaitOnChan")
            /\ status' = "Cancelling"
            /\ ctx_cancelled' = ctx_cancelled \union {running}
            /\ running' = nil
            /\ global_chan' = Append(global_chan, empty_chan)
            /\ local_chan' = [local_chan EXCEPT ![n] = new_ch]
            /\ wait_list' = Append(wait_list, new_ch)

        when_cancelling ==
            /\ goto(n, "WaitOnChan")
            /\ global_chan' = Append(global_chan, empty_chan)
            /\ local_chan' = [local_chan EXCEPT ![n] = new_ch]
            /\ UNCHANGED status
            /\ UNCHANGED running
            /\ UNCHANGED ctx_cancelled
    IN
    /\ pc[n] = "Init"
    /\ IF status = "NoJob" THEN
            when_normal
        ELSE IF status = "Running" THEN
            when_running
        ELSE
            when_cancelling


RunJob(n) ==
    LET
        when_normal ==
            /\ UNCHANGED wait_list

        when_cancelling ==
            /\ wait_list' = Tail(wait_list)
    IN
    /\ pc[n] = "Running"
    /\ is_cancelled(n)
    /\ goto(n, "Terminated")
    /\ IF status = "Running" THEN
            when_normal
        ELSE
            when_cancelling

-----------------------------------------------------------------------

TerminateCond ==
    /\ \A n \in Node: pc[n] = "Terminated"

Terminated ==
    /\ TerminateCond
    /\ UNCHANGED vars


Next ==
    \/ \E n \in Node:
        \/ StartJob(n)
        \/ RunJob(n)
    \/ Terminated

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------

AtMostOneRunning ==
    LET
        running_set == {n \in Node: pc[n] ="Running"}
    IN
        Cardinality(running_set) <= 1

====

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

WaitEntry == [
    chan: Channel
]

-----------------------------------------------------------------------

TypeOK ==
    /\ pc \in [Node -> PC]
    /\ global_chan \in Seq(ChannelData)
    /\ status \in {"NoJob", "Running", "Cancelling"}
    /\ running \in NullNode
    /\ wait_list \in Seq(WaitEntry)
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
        when_normal_no_wait ==
            /\ goto(n, "Running")
            /\ running' = n
            /\ status' = "Running"
            /\ UNCHANGED global_chan
            /\ UNCHANGED local_chan
            /\ UNCHANGED ctx_cancelled
            /\ UNCHANGED wait_list

        when_normal_with_wait_list ==
            /\ goto(n, "Running")
            /\ status' = "Cancelling"
            /\ ctx_cancelled' = ctx_cancelled \union {n}
            /\ UNCHANGED running
            /\ UNCHANGED wait_list
            /\ UNCHANGED global_chan
            /\ UNCHANGED local_chan

        when_normal ==
            IF wait_list = <<>>
                THEN when_normal_no_wait
                ELSE when_normal_with_wait_list

        new_ch == Len(global_chan')

        new_wait == [
            chan |-> new_ch
        ]

        when_running ==
            /\ goto(n, "WaitOnChan")
            /\ status' = "Cancelling"
            /\ ctx_cancelled' = ctx_cancelled \union {running}
            /\ running' = nil
            /\ global_chan' = Append(global_chan, empty_chan)
            /\ local_chan' = [local_chan EXCEPT ![n] = new_ch]
            /\ wait_list' = Append(wait_list, new_wait)

        when_cancelling ==
            /\ goto(n, "WaitOnChan")
            /\ global_chan' = Append(global_chan, empty_chan)
            /\ local_chan' = [local_chan EXCEPT ![n] = new_ch]
            /\ wait_list' = Append(wait_list, new_wait)
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

        wait == wait_list[1]
        ch == wait.chan

        when_cancelling ==
            /\ status' = "NoJob"
            /\ wait_list' = Tail(wait_list)
            /\ global_chan' = [global_chan EXCEPT ![ch].data = Append(@, "OK")]
            /\ UNCHANGED ctx_cancelled
            /\ UNCHANGED running
            /\ UNCHANGED local_chan
    IN
    /\ pc[n] = "Running"
    /\ is_cancelled(n)
    /\ goto(n, "Terminated")
    /\ IF status = "Running" THEN
            when_normal
        ELSE
            when_cancelling


WaitOnChan(n) ==
    LET
        ch == local_chan[n]
    IN
    /\ pc[n] = "WaitOnChan"
    /\ global_chan[ch].data # <<>>
    /\ goto(n, "Init")
    /\ global_chan' = [global_chan EXCEPT ![ch].data = Tail(@)]
    /\ local_chan' = [local_chan EXCEPT ![n] = nil]
    /\ UNCHANGED ctx_cancelled
    /\ UNCHANGED running
    /\ UNCHANGED status
    /\ UNCHANGED wait_list

-----------------------------------------------------------------------

TerminateCond ==
    /\ \A n \in Node:
        \/ pc[n] = "Terminated"
        \/ /\ pc[n] = "Running"
           /\ ~is_cancelled(n)

Terminated ==
    /\ TerminateCond
    /\ UNCHANGED vars


Next ==
    \/ \E n \in Node:
        \/ StartJob(n)
        \/ RunJob(n)
        \/ WaitOnChan(n)
    \/ Terminated

Spec == Init /\ [][Next]_vars

FairSpec == Spec /\ WF_vars(Next)

-----------------------------------------------------------------------

AlwaysTerminate == []<>TerminateCond


AtMostOneRunning ==
    LET
        running_set == {n \in Node: pc[n] ="Running"}
    IN
        Cardinality(running_set) <= 1


StatusRunningInv ==
    \/ /\ status \in {"NoJob", "Cancelling"}
       /\ running = nil
    \/ /\ status \in {"Running"}
       /\ running # nil

====

------ MODULE OnceRunner ----
EXTENDS TLC, FiniteSets, Naturals, Sequences

CONSTANTS Node, nil

VARIABLES
    pc, global_chan, status, running,
    wait_list, local_chan, ctx_cancelled, stop_cancel

vars == <<
    pc, global_chan, status, running,
    wait_list, local_chan, ctx_cancelled, stop_cancel
>>

-----------------------------------------------------------------------

Range(f) == {f[x]: x \in DOMAIN f}

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
    /\ stop_cancel \in BOOLEAN


Init ==
    /\ pc = [n \in Node |-> "Init"]
    /\ global_chan = <<>>
    /\ status = "NoJob"
    /\ running = nil
    /\ wait_list = <<>>
    /\ local_chan = [n \in Node |-> nil]
    /\ ctx_cancelled = {}
    /\ stop_cancel = FALSE

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

        append_to_wait_list ==
            /\ global_chan' = Append(global_chan, empty_chan)
            /\ local_chan' = [local_chan EXCEPT ![n] = new_ch]
            /\ wait_list' = Append(wait_list, new_ch)

        when_running ==
            /\ goto(n, "WaitOnChan")
            /\ status' = "Cancelling"
            /\ ctx_cancelled' = ctx_cancelled \union {running}
            /\ running' = nil
            /\ append_to_wait_list

        when_cancelling ==
            /\ goto(n, "WaitOnChan")
            /\ append_to_wait_list
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
    /\ UNCHANGED stop_cancel


notify_wait_list ==
    LET
        ch == wait_list[1]
    IN
    IF wait_list = <<>> THEN
        /\ UNCHANGED wait_list
        /\ UNCHANGED global_chan
    ELSE
        /\ wait_list' = Tail(wait_list)
        /\ global_chan' = [global_chan EXCEPT ![ch].data = Append(@, "OK")]


RunJob(n) ==
    LET
        when_normal ==
            /\ status' = "NoJob"
            /\ running' = nil
            /\ notify_wait_list
            /\ UNCHANGED ctx_cancelled
            /\ UNCHANGED local_chan
    IN
    /\ pc[n] = "Running"
    /\ is_cancelled(n)
    /\ goto(n, "Terminated")
    /\ when_normal
    /\ UNCHANGED stop_cancel


WaitOnChan(n) ==
    LET
        ch == local_chan[n]

        when_normal ==
            /\ global_chan[ch].data # <<>>
            /\ goto(n, "Init")
            /\ global_chan' = [global_chan EXCEPT ![ch].data = Tail(@)]
            /\ UNCHANGED wait_list

        filter_fn(e) == e # ch

        remove_from_wait_list_or_notify ==
            IF ch \in Range(wait_list) THEN
                /\ wait_list' = SelectSeq(wait_list, filter_fn)
                /\ UNCHANGED global_chan
            ELSE
                notify_wait_list

        when_cancelled ==
            /\ is_cancelled(n)
            /\ goto(n, "Terminated")
            /\ remove_from_wait_list_or_notify
    IN
    /\ pc[n] = "WaitOnChan"
    /\ \/ when_normal
       \/ when_cancelled
    /\ local_chan' = [local_chan EXCEPT ![n] = nil]
    /\ UNCHANGED ctx_cancelled
    /\ UNCHANGED <<status, running>>
    /\ UNCHANGED stop_cancel


EnableStopCancel ==
    /\ ~stop_cancel
    /\ stop_cancel' = TRUE
    /\ UNCHANGED pc
    /\ UNCHANGED <<status, running, wait_list>>
    /\ UNCHANGED global_chan
    /\ UNCHANGED local_chan
    /\ UNCHANGED ctx_cancelled


CancelContext(n) ==
    /\ ~stop_cancel
    /\ n \notin ctx_cancelled
    /\ ctx_cancelled' = ctx_cancelled \union {n}
    /\ UNCHANGED <<status, running, wait_list>>
    /\ UNCHANGED pc
    /\ UNCHANGED stop_cancel
    /\ UNCHANGED global_chan
    /\ UNCHANGED local_chan

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
        \/ CancelContext(n)
    \/ EnableStopCancel
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


StoppedCancelLeadToRunning ==
    LET
        running_set == {n \in Node: pc[n] ="Running"}

        num_running == Cardinality(running_set)

        pre_cond ==
            /\ stop_cancel
            /\ ctx_cancelled = {}

        cond ==
            /\ TerminateCond
            /\ num_running = 1
    IN
        pre_cond ~> cond


StatusRunningInv ==
    \/ /\ status \in {"NoJob", "Cancelling"}
       /\ running = nil
    \/ /\ status \in {"Running"}
       /\ running # nil


WhenTerminatedInv ==
    \A n \in Node:
        pc[n] = "Terminated" =>
            /\ local_chan[n] = nil


ChannelInv ==
    \A ch \in Channel:
        Len(global_chan[ch].data) <= 1

====

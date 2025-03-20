------ MODULE RateLimit ----
EXTENDS TLC, Naturals, FiniteSets, Sequences

CONSTANTS Node, nil, max_running

VARIABLES pc, state, global_chan, local_chan

vars == <<pc, state, global_chan, local_chan>>

---------------------------------------------------------------------------------

WaitStatus == {"OK", "Error"}

ChannelData == [
    data: Seq(WaitStatus)
]

Channel == DOMAIN global_chan

NullChannel == Channel \union {nil}

State == [
    running: Nat,
    wait_list: Seq(Channel)
]

NullState == State \union {nil}

PC == {"Init", "HandleRequest", "WaitOnChan", "Terminated"}

---------------------------------------------------------------------------------

TypeOK ==
    /\ pc \in [Node -> PC]
    /\ state \in NullState
    /\ global_chan \in Seq(ChannelData)
    /\ local_chan \in [Node -> NullChannel]

Init ==
    /\ pc = [n \in Node |-> "Init"]
    /\ state = nil
    /\ global_chan = <<>>
    /\ local_chan = [n \in Node |-> nil]

---------------------------------------------------------------------------------

goto(n, l) ==
    pc' = [pc EXCEPT ![n] = l]


NodeWait(n) ==
    LET
        old_state ==
            IF state = nil
                THEN [running |-> 0, wait_list |-> <<>>]
                ELSE state

        when_normal ==
            /\ goto(n, "HandleRequest")
            /\ state' = [old_state EXCEPT !.running = @ + 1]
            /\ UNCHANGED global_chan
            /\ UNCHANGED local_chan

        new_chan == [
            data |-> <<>>
        ]

        new_chan_addr == Len(global_chan')

        when_limit_running ==
            /\ goto(n, "WaitOnChan")
            /\ global_chan' = Append(global_chan, new_chan)
            /\ local_chan' = [local_chan EXCEPT ![n] = new_chan_addr]
            /\ state' = [state EXCEPT !.wait_list = Append(@, new_chan_addr)]
    IN
    /\ pc[n] = "Init"
    /\ IF old_state.running < max_running
        THEN when_normal
        ELSE when_limit_running


WaitOnChan(n) ==
    LET
        ch == local_chan[n]

        st == global_chan[ch].data[1]

        when_chan_non_empty ==
            /\ global_chan[ch].data # <<>>
            /\ global_chan' = [global_chan EXCEPT ![ch].data = Tail(@)]
    IN
    /\ pc[n] = "WaitOnChan"
    /\ when_chan_non_empty


HandleRequest(n) ==
    LET
        state_dec == [state EXCEPT !.running = @ - 1]

        when_no_wait ==
            /\ state' = state_dec
            /\ UNCHANGED global_chan

        ch == state.wait_list[1]

        when_waiting ==
            /\ state' = [state_dec EXCEPT !.wait_list = Tail(@)]
            /\ global_chan' = [global_chan EXCEPT ![ch].data = Append(@, "OK")]
    IN
    /\ pc[n] = "HandleRequest"
    /\ goto(n, "Terminated")
    /\ IF state.wait_list = <<>>
        THEN when_no_wait
        ELSE when_waiting
    /\ UNCHANGED local_chan

---------------------------------------------------------------------------------

TerminateCond ==
    /\ \A n \in Node: pc[n] = "Terminated"

Terminated ==
    /\ TerminateCond
    /\ UNCHANGED vars


Next ==
    \/ \E n \in Node:
        \/ NodeWait(n)
        \/ WaitOnChan(n)
        \/ HandleRequest(n)
    \/ Terminated


Spec == Init /\ [][Next]_vars

---------------------------------------------------------------------------------

MaxNumRunningInv ==
    LET
        running_set == {n \in Node: pc[n] = "HandleRequest"}
    IN
        Cardinality(running_set) <= max_running

====

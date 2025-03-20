------ MODULE RateLimit ----
EXTENDS TLC, Naturals, FiniteSets, Sequences

CONSTANTS Node, nil, max_running, max_wait_list

VARIABLES pc, state, global_chan, local_chan, stop_cancel

vars == <<pc, state, global_chan, local_chan, stop_cancel>>

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
    /\ stop_cancel \in BOOLEAN

Init ==
    /\ pc = [n \in Node |-> "Init"]
    /\ state = nil
    /\ global_chan = <<>>
    /\ local_chan = [n \in Node |-> nil]
    /\ stop_cancel = FALSE

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

        chan_with_data == [
            data |-> <<"Error">>
        ]

        when_reach_wait_list_limit ==
            /\ goto(n, "WaitOnChan")
            /\ global_chan' = Append(global_chan, chan_with_data)
            /\ local_chan' = [local_chan EXCEPT ![n] = new_chan_addr]
            /\ UNCHANGED state
    IN
    /\ pc[n] = "Init"
    /\ IF old_state.running < max_running THEN
            when_normal
        ELSE IF Len(old_state.wait_list) < max_wait_list THEN
            when_limit_running
        ELSE
            when_reach_wait_list_limit
    /\ UNCHANGED stop_cancel


WaitOnChan(n) ==
    LET
        ch == local_chan[n]

        st == global_chan[ch].data[1]

        when_status_ok ==
            /\ goto(n, "Init")

        when_status_error ==
            /\ goto(n, "Terminated")

        when_chan_non_empty ==
            /\ global_chan[ch].data # <<>>
            /\ global_chan' = [global_chan EXCEPT ![ch].data = Tail(@)]
            /\ IF st = "OK"
                THEN when_status_ok
                ELSE when_status_error
            /\ local_chan' = [local_chan EXCEPT ![n] = nil]
            /\ UNCHANGED state

        when_context_cancelled ==
            /\ ~stop_cancel
            /\ goto(n, "Terminated")
            /\ local_chan' = [local_chan EXCEPT ![n] = nil]
            /\ UNCHANGED global_chan
            /\ UNCHANGED state
    IN
    /\ pc[n] = "WaitOnChan"
    /\ \/ when_chan_non_empty
       \/ when_context_cancelled
    /\ UNCHANGED stop_cancel


HandleRequest(n) ==
    LET
        state_dec == [state EXCEPT !.running = @ - 1]

        when_no_wait ==
            /\ IF state_dec.running = 0
                THEN state' = nil
                ELSE state' = state_dec
            /\ UNCHANGED global_chan

        ch == state.wait_list[1]

        state_removed == [state_dec EXCEPT !.wait_list = Tail(@)]

        can_set_nil ==
            /\ state_removed.running = 0
            /\ state_removed.wait_list = <<>>

        when_waiting ==
            /\ IF can_set_nil
                THEN state' = nil
                ELSE state' = state_removed
            /\ global_chan' = [global_chan EXCEPT ![ch].data = Append(@, "OK")]
    IN
    /\ pc[n] = "HandleRequest"
    /\ goto(n, "Terminated")
    /\ IF state.wait_list = <<>>
        THEN when_no_wait
        ELSE when_waiting
    /\ UNCHANGED local_chan
    /\ UNCHANGED stop_cancel


StopContextCancel ==
    /\ ~stop_cancel
    /\ stop_cancel' = TRUE
    /\ UNCHANGED global_chan
    /\ UNCHANGED pc
    /\ UNCHANGED local_chan
    /\ UNCHANGED state

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
    \/ StopContextCancel
    \/ Terminated


Spec == Init /\ [][Next]_vars

FairSpec == Spec /\ WF_vars(Next)

---------------------------------------------------------------------------------

AlwaysTerminate == []<>TerminateCond

MaxNumRunningInv ==
    LET
        running_set == {n \in Node: pc[n] = "HandleRequest"}
    IN
        Cardinality(running_set) <= max_running


MaxWaitListInv ==
    state # nil => Len(state.wait_list) <= max_wait_list


ChannelInv ==
    \A ch \in Channel:
        Len(global_chan[ch].data) <= 1


WhenTerminateInv ==
    TerminateCond =>
        /\ \A n \in Node: local_chan[n] = nil
        /\ state = nil

====

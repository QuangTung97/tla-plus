------ MODULE TriggerLogic ----
EXTENDS TLC, Naturals, Sequences

CONSTANTS Client, Group, nil, max_val

VARIABLES pc, wait_list, closed, next_val,
    pushed, handled,
    observer, all_chan, local_chan

vars == <<pc, wait_list, closed, next_val,
    pushed, handled,
    observer, all_chan, local_chan>>

hist_vars == <<pushed, handled>>

-----------------------------------------------------------------------

Value == 20..29

PC == {"Init", "GetChan", "WaitChan", "DoTerminate", "Terminated"}

Channel == [
    data: Seq(Value),
    closed: BOOLEAN
]

ChanAddr == DOMAIN all_chan

NullChanAddr == ChanAddr \union {nil}

Observer == [
    group: Group,
    chan: NullChanAddr,
    pending: Seq(Value)
]

NullObserver == Observer \union {nil}

TypeOK ==
    /\ pc \in [Client -> PC]
    /\ wait_list \in [Group -> SUBSET Client]
    /\ closed \in BOOLEAN
    /\ next_val \in 20..max_val

    /\ pushed \in [Group -> Seq(Value)]
    /\ handled \in [Client -> [Group -> Seq(Value)]]

    /\ observer \in [Client -> NullObserver]
    /\ all_chan \in Seq(Channel)
    /\ local_chan \in [Client -> NullChanAddr]


Init ==
    /\ pc = [c \in Client |-> "Init"]
    /\ wait_list = [g \in Group |-> {}]
    /\ closed = FALSE
    /\ next_val = 20

    /\ pushed = [g \in Group |-> <<>>]
    /\ handled = [c \in Client |-> [g \in Group |-> <<>>]]

    /\ observer = [c \in Client |-> nil]
    /\ all_chan = <<>>
    /\ local_chan = [c \in Client |-> nil]

-----------------------------------------------------------------------

push_to_addr_list(addr_list, val) ==
    LET
        update(old, addr) ==
            IF addr \in addr_list
                THEN [old EXCEPT !.data = Append(@, val)]
                ELSE old
    IN
        all_chan' = [addr \in DOMAIN all_chan |-> update(all_chan[addr], addr)]


clear_observer_chan(old_obs, clear_set) ==
    LET
        update(old, c) ==
            IF c \in clear_set
                THEN [old EXCEPT !.chan = nil]
                ELSE old
    IN
        [c \in DOMAIN old_obs |-> update(old_obs[c], c)]


observer_append_pending(old_obs, update_set, val) ==
    LET
        update(old, c) ==
            IF c \in update_set
                THEN [old EXCEPT !.pending = Append(@, val)]
                ELSE old
    IN
        [c \in DOMAIN old_obs |-> update(old_obs[c], c)]


Trigger(g) ==
    LET
        allow_push_set == {c \in wait_list[g]: observer[c].chan # nil}

        push_addr == {observer[c].chan: c \in allow_push_set}

        push_to_wait_list ==
            /\ push_to_addr_list(push_addr, next_val')
            /\ observer' = observer_append_pending(
                    clear_observer_chan(observer, allow_push_set),
                    wait_list[g] \ allow_push_set,
                    next_val'
                )
    IN
    /\ next_val < max_val
    /\ next_val' = next_val + 1
    /\ ~closed
    /\ wait_list[g] # {}

    /\ pushed' = [pushed EXCEPT ![g] = Append(@, next_val')]
    /\ push_to_wait_list

    /\ UNCHANGED closed
    /\ UNCHANGED pc
    /\ UNCHANGED wait_list
    /\ UNCHANGED local_chan
    /\ UNCHANGED handled


goto(c, l) ==
    pc' = [pc EXCEPT ![c] = l]

NewObserver(c, g) ==
    LET
        new_obs == [
            group |-> g,
            chan |-> nil,
            pending |-> <<>>
        ]
    IN
    /\ pc[c] = "Init"
    /\ goto(c, "GetChan")

    /\ observer' = [observer EXCEPT ![c] = new_obs]
    /\ wait_list' = [wait_list EXCEPT ![g] = @ \union {c}]

    /\ UNCHANGED closed
    /\ UNCHANGED all_chan
    /\ UNCHANGED local_chan
    /\ UNCHANGED hist_vars
    /\ UNCHANGED next_val


GetChan(c) ==
    LET
        new_chan == [
            data |-> <<>>,
            closed |-> FALSE
        ]

        addr == Len(all_chan')

        when_pending_empty ==
            /\ observer[c].pending = <<>>
            /\ ~closed
            /\ all_chan' = Append(all_chan, new_chan)
            /\ observer' = [observer EXCEPT ![c].chan = addr]

        val == observer[c].pending[1]

        new_chan_with_val == [
            data |-> <<val>>,
            closed |-> FALSE
        ]

        when_pending_non_empty ==
            /\ observer[c].pending # <<>>
            /\ all_chan' = Append(all_chan, new_chan_with_val)
            /\ observer' = [observer EXCEPT ![c].pending = Tail(@)]

        new_closed_chan == [
            data |-> <<>>,
            closed |-> TRUE
        ]

        when_closed ==
            /\ observer[c].pending = <<>>
            /\ closed
            /\ all_chan' = Append(all_chan, new_closed_chan)
            /\ UNCHANGED observer
    IN
    /\ pc[c] = "GetChan"

    /\ goto(c, "WaitChan")

    /\ \/ when_pending_empty
       \/ when_pending_non_empty
       \/ when_closed

    /\ local_chan' = [local_chan EXCEPT ![c] = addr]

    /\ UNCHANGED closed
    /\ UNCHANGED hist_vars
    /\ UNCHANGED wait_list
    /\ UNCHANGED next_val


WaitChan(c) ==
    LET
        addr == local_chan[c]

        g == observer[c].group

        val == all_chan[addr].data[1]

        when_non_empty ==
            /\ all_chan[addr].data # <<>>
            /\ goto(c, "GetChan")
            /\ all_chan' = [all_chan EXCEPT ![addr].data = Tail(@)]
            /\ handled' = [handled EXCEPT ![c][g] = Append(@, val)]
            /\ local_chan' = [local_chan EXCEPT ![c] = nil]

        when_closed ==
            /\ all_chan[addr].data = <<>>
            /\ all_chan[addr].closed
            /\ goto(c, "DoTerminate")
            /\ local_chan' = [local_chan EXCEPT ![c] = nil]
            /\ UNCHANGED handled
            /\ UNCHANGED all_chan
    IN
    /\ pc[c] = "WaitChan"

    /\ \/ when_non_empty
       \/ when_closed

    /\ UNCHANGED observer
    /\ UNCHANGED closed
    /\ UNCHANGED pushed
    /\ UNCHANGED wait_list
    /\ UNCHANGED next_val


DoTerminate(c) ==
    LET
        g == observer[c].group
    IN
    /\ pc[c] = "DoTerminate"
    /\ goto(c, "Terminated")

    /\ wait_list' = [wait_list EXCEPT ![g] = @ \ {c}]

    /\ UNCHANGED observer
    /\ UNCHANGED next_val
    /\ UNCHANGED local_chan
    /\ UNCHANGED all_chan
    /\ UNCHANGED hist_vars
    /\ UNCHANGED closed


close_chan_addr_list(addr_list) ==
    LET
        update(old, addr) ==
            IF addr \in addr_list
                THEN [old EXCEPT !.closed = TRUE]
                ELSE old
    IN
        all_chan' = [addr \in DOMAIN all_chan |-> update(all_chan[addr], addr)]


Shutdown ==
    LET
        all_wait_list == UNION {wait_list[g]: g \in Group}

        allow_close_set == {c \in all_wait_list: observer[c].chan # nil}

        close_addr == {observer[c].chan: c \in allow_close_set}
    IN
    /\ ~closed
    /\ closed' = TRUE
    /\ next_val' = max_val

    /\ close_chan_addr_list(close_addr)
    /\ observer' = clear_observer_chan(observer, allow_close_set)

    /\ UNCHANGED hist_vars
    /\ UNCHANGED wait_list
    /\ UNCHANGED <<pc, local_chan>>


TerminateCond ==
    /\ \A c \in Client: pc[c] = "Terminated"
    /\ closed = TRUE


Terminated ==
    /\ TerminateCond
    /\ UNCHANGED vars


Next ==
    \/ \E g \in Group:
        \/ Trigger(g)

    \/ \E c \in Client, g \in Group:
        \/ NewObserver(c, g)

    \/ \E c \in Client:
        \/ GetChan(c)
        \/ WaitChan(c)
        \/ DoTerminate(c)

    \/ Shutdown
    \/ Terminated

Spec == Init /\ [][Next]_vars

FairSpec == Spec /\ WF_vars(Next)

-----------------------------------------------------------------------

AlwaysTerminate == <> TerminateCond

ChannelOnlyMaxSizeOne ==
    \A idx \in DOMAIN all_chan:
        Len(all_chan[idx].data) <= 1


BeforeGetChanInv ==
    \A c \in Client:
        pc[c] = "GetChan" =>
            /\ local_chan[c] = nil
            /\ observer[c].chan = nil


ValueInv ==
    LET
        cond ==
            \A g \in Group: \E c \in Client:
                handled[c][g] = pushed[g]
    IN
        TerminateCond => cond


StateWhenTerminated ==
    LET
        cond ==
            /\ \A g \in Group: wait_list[g] = {}
            /\ \A c \in Client:
                /\ observer[c].chan = nil
                /\ observer[c].pending = <<>>
                /\ local_chan[c] = nil
            /\ next_val = max_val
    IN
        TerminateCond => cond

====

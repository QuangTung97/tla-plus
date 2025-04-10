---- MODULE PushList ----
EXTENDS TLC, Sequences, Naturals, FiniteSets

CONSTANTS Node, nil, max_set_error

----------------------------------------------------------------------------

VARIABLES
    pc, next_action, push_list,
    global_chan, local_chan, num_leader, handled,
    last_error, num_set_error

vars == <<
    pc, next_action, push_list,
    global_chan, local_chan, num_leader, handled,
    last_error, num_set_error
>>

----------------------------------------------------------------------------

MapSeq(seq, fn(_)) ==
    [x \in DOMAIN seq |-> fn(seq[x])]

Range(f) == {f[x]: x \in DOMAIN f}

IsUnique(seq) ==
    Cardinality(Range(seq)) = Len(seq)

----------------------------------------------------------------------------

Action == 21..29

ChannelData == Seq({"empty"})

PC == {"Init", "HandleQueue", "WaitChan", "Terminated"}

Channel == DOMAIN global_chan
NullChan == Channel \union {nil}

PushEntry == [
    action: Action,
    resp_chan: Channel
]

----------------------------------------------------------------------------

TypeOK ==
    /\ pc \in [Node -> PC]
    /\ next_action \in (Action \union {20})
    /\ push_list \in Seq(PushEntry)
    /\ num_leader \in 0..10
    /\ global_chan \in Seq(ChannelData)
    /\ local_chan \in [Node -> NullChan]
    /\ handled \in Seq(Action)
    /\ last_error \in BOOLEAN
    /\ num_set_error \in 0..max_set_error

Init ==
    /\ pc = [n \in Node |-> "Init"]
    /\ next_action = 20
    /\ push_list = <<>>
    /\ num_leader = 0
    /\ global_chan = <<>>
    /\ local_chan = [n \in Node |-> nil]
    /\ handled = <<>>
    /\ last_error = FALSE
    /\ num_set_error = 0

----------------------------------------------------------------------------

goto(n, l) ==
    pc' = [pc EXCEPT ![n] = l]


Start(n) ==
    LET
        new_chan == <<>>

        addr == Len(global_chan')

        e == [
            action |-> next_action',
            resp_chan |-> addr
        ]

        is_leader ==
            /\ goto(n, "HandleQueue")
            /\ num_leader' = num_leader + 1

        is_not_leader ==
            /\ goto(n, "WaitChan")
            /\ UNCHANGED num_leader
    IN
    /\ pc[n] = "Init"

    /\ next_action' = next_action + 1
    /\ global_chan' = Append(global_chan, new_chan)
    /\ local_chan' = [local_chan EXCEPT ![n] = addr]
    /\ push_list' = Append(push_list, e)

    /\ IF push_list = <<>> \/ last_error
        THEN is_leader
        ELSE is_not_leader
    /\ UNCHANGED handled
    /\ UNCHANGED last_error
    /\ UNCHANGED num_set_error


pushToChannels(list) ==
    LET
        resp_fn(e) == e.resp_chan
        push_addrs == Range(MapSeq(list, resp_fn))

        push_to(addr, old) ==
            IF addr \in push_addrs
                THEN Append(old, "empty")
                ELSE old
    IN
    global_chan' = [
        addr \in Channel |-> push_to(addr, global_chan[addr])]

HandleQueue(n) ==
    LET
        when_empty ==
            /\ UNCHANGED push_list
            /\ UNCHANGED handled
            /\ UNCHANGED global_chan

        entry == push_list[1]

        when_error ==
            /\ push_list' = Tail(push_list)
            /\ handled' = Append(handled, entry.action)
            /\ pushToChannels(<<entry>>)

        map_fn(e) == e.action
        all_actions == MapSeq(push_list, map_fn)

        when_normal ==
            /\ push_list' = <<>>
            /\ handled' = handled \o all_actions
            /\ pushToChannels(push_list)
    IN
    /\ pc[n] = "HandleQueue"
    /\ goto(n, "WaitChan")
    /\ num_leader' = num_leader - 1
    /\ IF push_list = <<>> THEN
            when_empty
        ELSE IF last_error /\ num_leader' > 0 THEN
            when_error
        ELSE
            when_normal
    /\ UNCHANGED next_action
    /\ UNCHANGED local_chan
    /\ UNCHANGED last_error
    /\ UNCHANGED num_set_error


WaitChan(n) ==
    LET
        addr == local_chan[n]
    IN
    /\ pc[n] = "WaitChan"
    /\ goto(n, "Terminated")
    /\ global_chan[addr] # <<>>
    /\ global_chan' = [global_chan EXCEPT ![addr] = Tail(@)]
    /\ local_chan' = [local_chan EXCEPT ![n] = nil]
    /\ UNCHANGED next_action
    /\ UNCHANGED push_list
    /\ UNCHANGED handled
    /\ UNCHANGED last_error
    /\ UNCHANGED num_set_error
    /\ UNCHANGED num_leader


UpdateLastError ==
    LET
        update_to_true ==
            /\ ~last_error
            /\ num_set_error < max_set_error
            /\ num_set_error' = num_set_error + 1
            /\ last_error' = TRUE

        update_to_false ==
            /\ last_error
            /\ last_error' = FALSE
            /\ UNCHANGED num_set_error
    IN
    /\ \/ update_to_true
       \/ update_to_false
    /\ UNCHANGED global_chan
    /\ UNCHANGED <<pc, local_chan, push_list>>
    /\ UNCHANGED <<handled, next_action>>
    /\ UNCHANGED num_leader

----------------------------------------------------------------------------

TerminateCond ==
    /\ \A n \in Node: pc[n] = "Terminated"
    /\ num_set_error = max_set_error
    /\ last_error = FALSE

Terminated ==
    /\ TerminateCond
    /\ UNCHANGED vars


Next ==
    \/ \E n \in Node:
        \/ Start(n)
        \/ HandleQueue(n)
        \/ WaitChan(n)
    \/ UpdateLastError
    \/ Terminated

Spec == Init /\ [][Next]_vars

FairSpec == Spec /\ WF_vars(Next)

----------------------------------------------------------------------------

AlwaysTerminate == []<>TerminateCond


ChannelInv ==
    \A addr \in Channel:
        Len(global_chan[addr]) <= 1


TerminateInv ==
    TerminateCond =>
        /\ IsUnique(handled)
        /\ Len(handled) = Cardinality(Node)
        /\ num_leader = 0


====

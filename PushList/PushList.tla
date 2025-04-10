---- MODULE PushList ----
EXTENDS TLC, Sequences, Naturals, FiniteSets

CONSTANTS Node, nil

----------------------------------------------------------------------------

VARIABLES
    pc, next_action, push_list,
    global_chan, local_chan, handled

vars == <<
    pc, next_action, push_list,
    global_chan, local_chan, handled
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
    /\ global_chan \in Seq(ChannelData)
    /\ local_chan \in [Node -> NullChan]
    /\ handled \in Seq(Action)

Init ==
    /\ pc = [n \in Node |-> "Init"]
    /\ next_action = 20
    /\ push_list = <<>>
    /\ global_chan = <<>>
    /\ local_chan = [n \in Node |-> nil]
    /\ handled = <<>>

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

        is_not_leader ==
            /\ goto(n, "WaitChan")
    IN
    /\ pc[n] = "Init"

    /\ next_action' = next_action + 1
    /\ global_chan' = Append(global_chan, new_chan)
    /\ local_chan' = [local_chan EXCEPT ![n] = addr]
    /\ push_list' = Append(push_list, e)

    /\ IF push_list = <<>>
        THEN is_leader
        ELSE is_not_leader
    /\ UNCHANGED handled


HandleQueue(n) ==
    LET
        map_fn(e) == e.action
        actions == MapSeq(push_list, map_fn)

        resp_fn(e) == e.resp_chan
        push_addrs == Range(MapSeq(push_list, resp_fn))

        push_to(addr, old) ==
            IF addr \in push_addrs
                THEN Append(old, "empty")
                ELSE old

        push_to_chans ==
            global_chan' = [
                addr \in Channel |-> push_to(addr, global_chan[addr])]
    IN
    /\ pc[n] = "HandleQueue"
    /\ goto(n, "WaitChan")
    /\ push_list' = <<>>
    /\ handled' = handled \o actions
    /\ push_to_chans
    /\ UNCHANGED next_action
    /\ UNCHANGED local_chan


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


----------------------------------------------------------------------------

TerminateCond ==
    /\ \A n \in Node: pc[n] = "Terminated"

Terminated ==
    /\ TerminateCond
    /\ UNCHANGED vars


Next ==
    \/ \E n \in Node:
        \/ Start(n)
        \/ HandleQueue(n)
        \/ WaitChan(n)
    \/ Terminated

Spec == Init /\ [][Next]_vars

----------------------------------------------------------------------------

ChannelInv ==
    \A addr \in Channel:
        Len(global_chan[addr]) <= 1


TerminateInv ==
    TerminateCond =>
        /\ IsUnique(handled)
        /\ Len(handled) = Cardinality(Node)

====

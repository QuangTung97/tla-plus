------ MODULE GenericSyncKV ----
EXTENDS TLC, Sequences, Naturals, FiniteSets

CONSTANTS Key, nil, max_action

VARIABLES
    state, next_val, num_action, update_list,
    global_chan, repl,
    pc, connected,
    wait_chan, local_update_list, local_changeset,
    local_chan

vars == <<
    state, next_val, num_action, update_list,
    global_chan, repl,
    pc, connected,
    wait_chan, local_update_list, local_changeset,
    local_chan
>>

---------------------------------------------------------------------------

Range(f) == {f[x]: x \in DOMAIN f}

IsUnique(s) ==
    Cardinality(Range(s)) = Len(s)

---------------------------------------------------------------------------

Value == 20..29

NullValue == Value \union {nil}

Chan == DOMAIN global_chan

NullChan == Chan \union {nil}

GetOutput == [
    key: Key,
    val: NullValue
]

ChanInfo == [
    data: Seq(GetOutput),
    closed: BOOLEAN
]

---------------------------------------------------------------------------

TypeOK ==
    /\ state \in [Key -> NullValue]
    /\ next_val \in Value
    /\ num_action \in 0..max_action
    /\ repl \in [Key -> NullValue]
    /\ update_list \in Seq(Key)

    /\ global_chan \in Seq(ChanInfo)

    /\ pc \in {"Init", "GetNew", "WaitOnChan"}
    /\ connected \in BOOLEAN
    /\ wait_chan \in NullChan
    /\ local_update_list \in Seq(Key)
    /\ local_changeset \subseteq Key
    /\ local_chan \in NullChan

Init ==
    /\ state = [k \in Key |-> nil]
    /\ next_val = 20
    /\ num_action = 0
    /\ repl = [k \in Key |-> nil]
    /\ update_list = <<>>
    /\ global_chan = <<>>

    /\ pc = "Init"
    /\ connected = FALSE
    /\ wait_chan = nil
    /\ local_update_list = <<>>
    /\ local_changeset = {}
    /\ local_chan = nil

---------------------------------------------------------------------------


pushChangeToClient(k) ==
    LET
        do_update_local_list ==
            IF k \in local_changeset THEN
                /\ UNCHANGED local_update_list
                /\ UNCHANGED local_changeset
            ELSE
                /\ local_update_list' = Append(local_update_list, k)
                /\ local_changeset' = local_changeset \union {k}

        when_wait_nil ==
            /\ UNCHANGED wait_chan
            /\ UNCHANGED global_chan
            /\ do_update_local_list

        new_elem == [
            key |-> k,
            val |-> state'[k]
        ]

        when_wait_non_nil ==
            /\ global_chan' = [global_chan EXCEPT
                    ![wait_chan].data = Append(@, new_elem)]
            /\ UNCHANGED local_update_list
            /\ UNCHANGED local_changeset
            /\ wait_chan' = nil

        when_connected ==
            IF wait_chan = nil
                THEN when_wait_nil
                ELSE when_wait_non_nil

        when_not_connected ==
            /\ UNCHANGED global_chan
            /\ UNCHANGED wait_chan
            /\ UNCHANGED local_update_list
            /\ UNCHANGED local_changeset
    IN
        IF connected
            THEN when_connected
            ELSE when_not_connected

UpdateState(k) ==
    LET
        v == next_val'
    IN
    /\ num_action < max_action
    /\ num_action' = num_action + 1
    /\ next_val' = next_val + 1
    /\ state' = [state EXCEPT ![k] = v]

    /\ IF state[k] = nil
        THEN update_list' = Append(update_list, k)
        ELSE UNCHANGED update_list

    /\ pushChangeToClient(k)

    /\ UNCHANGED <<pc, local_chan, connected>>
    /\ UNCHANGED repl


DeleteKey(k) ==
    LET
        filter_fn(x) == x # k
    IN
    /\ num_action < max_action
    /\ num_action' = num_action + 1
    /\ state[k] # nil
    /\ state' = [state EXCEPT ![k] = nil]

    /\ update_list' = SelectSeq(update_list, filter_fn)
    /\ pushChangeToClient(k)

    /\ UNCHANGED next_val
    /\ UNCHANGED <<pc, local_chan, connected>>
    /\ UNCHANGED repl

---------------------------------------------------------------------------

localUnchanged ==
    /\ UNCHANGED <<num_action, next_val>>
    /\ UNCHANGED <<state, update_list>>


InitSession ==
    /\ pc = "Init"
    /\ pc' = "GetNew"
    /\ connected' = TRUE
    /\ local_update_list' = update_list
    /\ local_changeset' = Range(update_list)
    /\ UNCHANGED wait_chan
    /\ UNCHANGED global_chan
    /\ UNCHANGED local_chan
    /\ UNCHANGED repl
    /\ localUnchanged


GetNew ==
    LET
        ch == Len(global_chan')

        empty_ch == [
            data |-> <<>>,
            closed |-> FALSE
        ]

        when_update_list_empty ==
            /\ UNCHANGED local_update_list
            /\ UNCHANGED local_changeset
            /\ global_chan' = Append(global_chan, empty_ch)
            /\ wait_chan' = ch

        k == local_update_list[1]

        new_elem == [
            key |-> k,
            val |-> state[k]
        ]

        non_empty_ch == [
            data |-> <<new_elem>>,
            closed |-> FALSE
        ]

        remove_from_update_list ==
            /\ local_update_list' = Tail(local_update_list)
            /\ local_changeset' = local_changeset \ {k}
            /\ global_chan' = Append(global_chan, non_empty_ch)
            /\ UNCHANGED wait_chan
    IN
    /\ pc = "GetNew"
    /\ pc' = "WaitOnChan"
    /\ IF local_update_list = <<>>
        THEN when_update_list_empty
        ELSE remove_from_update_list
    /\ local_chan' = ch

    /\ UNCHANGED repl
    /\ UNCHANGED connected
    /\ localUnchanged


ConsumeChan ==
    LET
        ch == local_chan
        e == global_chan[ch].data[1]
    IN
    /\ pc = "WaitOnChan"
    /\ pc' = "GetNew"
    /\ global_chan[ch].data # <<>>
    /\ global_chan' = [global_chan EXCEPT ![ch].data = Tail(@)]
    /\ local_chan' = nil

    /\ repl' = [repl EXCEPT ![e.key] = e.val]

    /\ UNCHANGED <<local_update_list, local_changeset>>
    /\ UNCHANGED connected
    /\ UNCHANGED wait_chan
    /\ localUnchanged

---------------------------------------------------------------------------

TerminateCond ==
    /\ num_action = max_action
    /\ pc = "Terminated"

Terminated ==
    /\ TerminateCond
    /\ UNCHANGED vars


Next ==
    \/ \E k \in Key:
        \/ UpdateState(k)
        \/ DeleteKey(k)
    \/ InitSession
    \/ GetNew
    \/ ConsumeChan
    \/ Terminated

Spec == Init /\ [][Next]_vars

FairSpec == Spec /\ WF_vars(Next)

---------------------------------------------------------------------------

AlwaysTerminate == []<>TerminateCond


TerminateInv ==
    TerminateCond =>
        /\ state = repl


ChannelInv ==
    \A ch \in Chan:
        Len(global_chan[ch].data) <= 1


ConnectedInv ==
    connected <=> pc # "Init"


InitInv ==
    pc = "Init" =>
        /\ connected = FALSE


UpdateListInv ==
    IsUnique(update_list)


LocalUpdateListInv ==
    /\ IsUnique(local_update_list)
    /\ Range(local_update_list) = local_changeset

====

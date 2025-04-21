------ MODULE GenericSyncKV ----
EXTENDS TLC, Sequences, Naturals, FiniteSets

CONSTANTS Key, nil, max_action

VARIABLES
    state, next_val, num_action, update_list,
    global_chan, repl, shutdown,
    pc, connected, client_finished,
    wait_chan, local_update_list, local_changeset,
    local_chan

vars == <<
    state, next_val, num_action, update_list,
    global_chan, repl, shutdown,
    pc, connected, client_finished,
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
    /\ shutdown \in BOOLEAN

    /\ global_chan \in Seq(ChanInfo)

    /\ pc \in {"Init", "GetNew", "WaitOnChan", "Terminated"}
    /\ connected \in BOOLEAN
    /\ client_finished \in BOOLEAN
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
    /\ shutdown = FALSE

    /\ pc = "Init"
    /\ connected = FALSE
    /\ client_finished = FALSE
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
    /\ ~shutdown
    /\ num_action' = num_action + 1
    /\ next_val' = next_val + 1
    /\ state' = [state EXCEPT ![k] = v]

    /\ IF state[k] = nil
        THEN update_list' = Append(update_list, k)
        ELSE UNCHANGED update_list

    /\ pushChangeToClient(k)

    /\ UNCHANGED <<pc, local_chan, connected, client_finished>>
    /\ UNCHANGED shutdown
    /\ UNCHANGED repl


DeleteKey(k) ==
    LET
        filter_fn(x) == x # k
    IN
    /\ num_action < max_action
    /\ ~shutdown
    /\ num_action' = num_action + 1
    /\ state[k] # nil
    /\ state' = [state EXCEPT ![k] = nil]

    /\ update_list' = SelectSeq(update_list, filter_fn)
    /\ pushChangeToClient(k)

    /\ UNCHANGED next_val
    /\ UNCHANGED <<pc, local_chan, connected, client_finished>>
    /\ UNCHANGED shutdown
    /\ UNCHANGED repl


close_wait_chan ==
    IF wait_chan = nil THEN
        /\ UNCHANGED global_chan
        /\ UNCHANGED wait_chan
    ELSE
        /\ global_chan' = [global_chan EXCEPT ![wait_chan].closed = TRUE]
        /\ wait_chan' = nil


Shutdown ==
    /\ ~shutdown
    /\ ~client_finished
    /\ shutdown' = TRUE
    /\ close_wait_chan
    /\ UNCHANGED <<local_changeset, local_update_list>>
    /\ UNCHANGED <<num_action, next_val>>
    /\ UNCHANGED <<pc, local_chan, connected, client_finished>>
    /\ UNCHANGED repl
    /\ UNCHANGED <<state, update_list>>

---------------------------------------------------------------------------

localUnchanged ==
    /\ UNCHANGED <<num_action, next_val>>
    /\ UNCHANGED <<state, update_list>>
    /\ UNCHANGED shutdown


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
    /\ UNCHANGED client_finished
    /\ localUnchanged


GetNew ==
    LET
        ch == Len(global_chan')

        closed_ch == [
            data |-> <<>>,
            closed |-> TRUE
        ]

        when_shutdown ==
            /\ UNCHANGED local_update_list
            /\ UNCHANGED local_changeset
            /\ global_chan' = Append(global_chan, closed_ch)
            /\ UNCHANGED wait_chan

        empty_ch == [
            data |-> <<>>,
            closed |-> FALSE
        ]

        when_update_list_empty_not_shutdown ==
            /\ UNCHANGED local_update_list
            /\ UNCHANGED local_changeset
            /\ global_chan' = Append(global_chan, empty_ch)
            /\ wait_chan' = ch

        when_update_list_empty ==
            IF shutdown \/ client_finished
                THEN when_shutdown
                ELSE when_update_list_empty_not_shutdown

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
    /\ UNCHANGED client_finished
    /\ localUnchanged


ConsumeChan ==
    LET
        ch == local_chan
        e == global_chan[ch].data[1]

        when_has_data ==
            /\ global_chan[ch].data # <<>>
            /\ pc' = "GetNew"
            /\ global_chan' = [global_chan EXCEPT ![ch].data = Tail(@)]
            /\ local_chan' = nil
            /\ repl' = [repl EXCEPT ![e.key] = e.val]

        when_closed ==
            /\ global_chan[ch].closed
            /\ pc' = "Terminated"
            /\ local_chan' = nil
            /\ UNCHANGED global_chan
            /\ UNCHANGED repl
    IN
    /\ pc = "WaitOnChan"
    /\ \/ when_has_data
       \/ when_closed

    /\ UNCHANGED <<local_update_list, local_changeset>>
    /\ UNCHANGED connected
    /\ UNCHANGED wait_chan
    /\ UNCHANGED client_finished
    /\ localUnchanged


ClientDoFinish ==
    /\ connected
    /\ ~client_finished
    /\ ~shutdown
    /\ client_finished' = TRUE
    /\ connected' = FALSE
    /\ close_wait_chan

    /\ UNCHANGED <<pc, repl>>
    /\ UNCHANGED <<local_chan, local_changeset, local_update_list>>
    /\ localUnchanged

---------------------------------------------------------------------------

TerminateCond ==
    /\ \/ shutdown
       \/ client_finished
    /\ pc = "Terminated"

Terminated ==
    /\ TerminateCond
    /\ UNCHANGED vars


Next ==
    \/ \E k \in Key:
        \/ UpdateState(k)
        \/ DeleteKey(k)
    \/ Shutdown
    \/ InitSession
    \/ GetNew
    \/ ConsumeChan
    \/ ClientDoFinish
    \/ Terminated

Spec == Init /\ [][Next]_vars

FairSpec == Spec /\ WF_vars(Next)

---------------------------------------------------------------------------

AlwaysTerminate == []<>TerminateCond


TerminateInv ==
    TerminateCond =>
        /\ ~client_finished => state = repl
        /\ local_chan = nil \* TODO


ChannelInv ==
    \A ch \in Chan:
        /\ Len(global_chan[ch].data) <= 1
        /\ global_chan[ch].closed => global_chan[ch].data = <<>>


ConnectedInv ==
    connected => pc # "Init"


InitInv ==
    pc = "Init" =>
        /\ connected = FALSE


UpdateListInv ==
    IsUnique(update_list)


LocalUpdateListInv ==
    /\ IsUnique(local_update_list)
    /\ Range(local_update_list) = local_changeset


ClientFinishInv ==
    client_finished => ~connected


NotAllowToCloseMultiTimes ==
    LET
        enable_cond ==
            /\ wait_chan # nil
            /\ \/ ENABLED Shutdown
               \/ ENABLED ClientDoFinish
    IN
        enable_cond => ~global_chan[wait_chan].closed

====

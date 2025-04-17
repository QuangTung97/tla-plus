------ MODULE GenericSyncKV ----
EXTENDS TLC, Sequences

CONSTANTS Key, Value, nil

VARIABLES
    state, update_list,
    global_chan, repl, pc,
    wait_chan, local_update_list,
    local_chan, stopped

vars == <<
    state, update_list,
    global_chan, repl, pc,
    wait_chan, local_update_list,
    local_chan, stopped
>>

---------------------------------------------------------------------------

NullValue == Value \union {nil}

Chan == DOMAIN global_chan

NullChan == Chan \union {nil}

GetOutput == [
    key: Key,
    val: Value
]

---------------------------------------------------------------------------

TypeOK ==
    /\ state \in [Key -> NullValue]
    /\ repl \in [Key -> NullValue]
    /\ update_list \in Seq(Key)

    /\ global_chan \in Seq(Seq(GetOutput))

    /\ pc \in {"Init", "GetNew", "WaitOnChan"}
    /\ wait_chan \in NullChan
    /\ local_update_list \in Seq(Key)
    /\ local_chan \in NullChan

    /\ stopped \in BOOLEAN

Init ==
    /\ state = [k \in Key |-> nil]
    /\ repl = [k \in Key |-> nil]
    /\ update_list = <<>>
    /\ global_chan = <<>>
    /\ pc = "Init"
    /\ wait_chan = nil
    /\ local_update_list = <<>>
    /\ local_chan = nil
    /\ stopped = FALSE

---------------------------------------------------------------------------

UpdateState(k, v) ==
    /\ ~stopped
    /\ state[k] # v
    /\ state' = [state EXCEPT ![k] = v]
    /\ update_list' = Append(update_list, k)

    /\ UNCHANGED global_chan
    /\ UNCHANGED wait_chan
    /\ UNCHANGED <<pc, local_chan, local_update_list>>
    /\ UNCHANGED repl
    /\ UNCHANGED stopped


StopUpdate ==
    /\ ~stopped
    /\ stopped' = TRUE
    /\ UNCHANGED global_chan
    /\ UNCHANGED wait_chan
    /\ UNCHANGED <<pc, local_chan, local_update_list>>
    /\ UNCHANGED <<state, repl, update_list>>

---------------------------------------------------------------------------

localUnchanged ==
    /\ UNCHANGED <<state, update_list>>
    /\ UNCHANGED stopped


InitSession ==
    /\ pc = "Init"
    /\ pc' = "GetNew"
    /\ local_update_list' = update_list
    /\ UNCHANGED wait_chan
    /\ UNCHANGED global_chan
    /\ UNCHANGED local_chan
    /\ UNCHANGED repl
    /\ localUnchanged


GetNew ==
    LET
        ch == Len(global_chan')

        when_update_list_empty ==
            /\ UNCHANGED local_update_list
            /\ global_chan' = Append(global_chan, <<>>)
            /\ wait_chan' = ch

        k == local_update_list[1]

        new_elem == [
            key |-> k,
            val |-> state[k]
        ]

        remove_from_update_list ==
            /\ local_update_list' = Tail(local_update_list)
            /\ global_chan' = Append(global_chan, <<new_elem>>)
            /\ UNCHANGED wait_chan
    IN
    /\ pc = "GetNew"
    /\ pc' = "WaitOnChan"
    /\ IF local_update_list = <<>>
        THEN when_update_list_empty
        ELSE remove_from_update_list
    /\ local_chan' = ch

    /\ UNCHANGED repl
    /\ localUnchanged

---------------------------------------------------------------------------

TerminateCond ==
    /\ stopped
    /\ pc = "WaitOnChan"
    /\ global_chan[local_chan] = <<>>

Terminated ==
    /\ TerminateCond
    /\ UNCHANGED vars


Next ==
    \/ \E k \in Key, v \in Value:
        \/ UpdateState(k, v)
    \/ InitSession
    \/ GetNew
    \/ StopUpdate
    \/ Terminated

Spec == Init /\ [][Next]_vars

---------------------------------------------------------------------------

TerminateInv ==
    TerminateCond =>
        /\ state = repl

====

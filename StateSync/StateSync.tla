------ MODULE StateSync ----
EXTENDS TLC, Integers, Sequences

CONSTANTS Key, Client, nil

VARIABLES server_state, client_states, next_val

vars == <<server_state, client_states, next_val>>

min_val == 21
max_val == 25

Value == min_val..max_val

NullValue == Value \union {nil}

TypeOK ==
    /\ server_state \in [Key -> NullValue]
    /\ next_val \in (min_val-1)..max_val


Init ==
    /\ server_state = [k \in Key |-> nil]
    /\ next_val = min_val - 1


TerminateCond ==
    /\ TRUE

Terminated ==
    /\ TerminateCond
    /\ UNCHANGED vars


Next ==
    \/ Terminated

====
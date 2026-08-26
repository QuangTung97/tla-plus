---- MODULE KVSync ----
EXTENDS TLC, Naturals, Sequences, FiniteSets

CONSTANTS Node, Key, Value, Conn, nil

VARIABLES
    state, conn_state,
    src_pc, dst_pc,
    stop_update

node_vars == <<
    src_pc, dst_pc
>>

aux_vars == <<
    stop_update
>>

vars == <<
    state, conn_state,
    node_vars,
    aux_vars
>>

---------------------------------------------------------------

Null(S) == S \union {nil}

---------------------------------------------------------------

SrcPC == {"Init"}

DstPC == {"Init"}

ConnState == [
    client_closed: BOOLEAN,
    server_closed: BOOLEAN
]

---------------------------------------------------------------

TypeOK ==
    /\ state \in [Key -> Null(Value)]
    /\ conn_state \in [Conn -> Null(ConnState)]

    /\ src_pc \in [Node -> SrcPC]
    /\ dst_pc \in [Node -> DstPC]

    /\ stop_update \in BOOLEAN

Init ==
    /\ state = [k \in Key |-> nil]
    /\ src_pc = [n \in Node |-> "Init"]
    /\ dst_pc = [n \in Node |-> "Init"]
    /\ conn_state = [c \in Conn |-> nil]

    /\ stop_update = FALSE

---------------------------------------------------------------

UpdateKV(k, v) ==
    /\ ~stop_update

    /\ state[k] # v
    /\ state' = [state EXCEPT ![k] = v]

    /\ UNCHANGED conn_state
    /\ UNCHANGED node_vars
    /\ UNCHANGED aux_vars

---------------------------------------------------------------

Terminated ==
    /\ UNCHANGED vars

---------------------------------------------------------------

Next ==
    \/ \E k \in Key, v \in Null(Value):
        \/ UpdateKV(k, v)
    \/ Terminated

Spec == Init /\ [][Next]_vars

---------------------------------------------------------------


====

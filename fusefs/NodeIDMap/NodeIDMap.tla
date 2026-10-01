---- MODULE NodeIDMap ----
EXTENDS TLC, Naturals, Sequences, FiniteSets

CONSTANTS Node, Key, nil

VARIABLES
    id_map, key_map, last_id,
    pc, local_id, local_key

local_vars == <<
    pc, local_id, local_key
>>

vars == <<
    id_map, key_map, last_id,
    local_vars
>>

--------------------------------------------------------------

Null(S) == S \union {nil}

--------------------------------------------------------------

ID == 10..(10 + Cardinality(Node))

Info == [
    key: Key,
    refcount: Nat
]

KeyInfo == [
    id: ID,
    refcount: Nat
]

PC == {"Init", "SetIDMap", "Process", "Terminated"}

--------------------------------------------------------------

TypeOK ==
    /\ id_map \in [ID -> Null(Info)]
    /\ key_map \in [Key -> Null(KeyInfo)]
    /\ last_id \in ID

    /\ pc \in [Node -> PC]
    /\ local_id \in [Node -> Null(ID)]
    /\ local_key \in [Node -> Null(Key)]

Init ==
    /\ id_map = [id \in ID |-> nil]
    /\ key_map = [key \in Key |-> nil]
    /\ last_id = 10

    /\ pc = [n \in Node |-> "Init"]
    /\ local_id = [n \in Node |-> nil]
    /\ local_key = [n \in Node |-> nil]

--------------------------------------------------------------

goto(n, l) ==
    pc' = [pc EXCEPT ![n] = l]

set_local(n, var, x) ==
    var' = [var EXCEPT ![n] = x]

--------------------------------------------------------------

AddKey(n, k) ==
    LET
        id == last_id'

        key_info == [
            id |-> id,
            refcount |-> 2
        ]

        when_not_exist ==
            /\ last_id' = last_id + 1
            /\ key_map' = [key_map EXCEPT ![k] = key_info]
            /\ set_local(n, local_id, id)

        when_exist ==
            /\ key_map' = [key_map EXCEPT ![k].refcount = @ + 1]
            /\ set_local(n, local_id, key_map[k].id)
            /\ UNCHANGED last_id
    IN
    /\ pc[n] = "Init"

    /\ set_local(n, local_key, k)
    /\ IF key_map[k] = nil
        THEN when_not_exist
        ELSE when_exist
    /\ goto(n, "SetIDMap")

    /\ UNCHANGED id_map

--------------------------------------------------------------

SetIDMap(n) ==
    LET
        id == local_id[n]
        k == local_key[n]

        info == [
            key |-> k,
            refcount |-> 1
        ]

        when_not_exist ==
            /\ id_map' = [id_map EXCEPT ![id] = info]

        when_exist ==
            /\ id_map' = [id_map EXCEPT ![id].refcount = @ + 1]
    IN
    /\ pc[n] = "SetIDMap"
    /\ goto(n, "Process")

    /\ IF id_map[id] = nil
        THEN when_not_exist
        ELSE when_exist

    /\ key_map' = [key_map EXCEPT ![k].refcount = @ - 1]

    /\ UNCHANGED last_id
    /\ UNCHANGED <<local_id, local_key>>

--------------------------------------------------------------

DeleteIDMap(n) ==
    LET
        id == local_id[n]
        k == local_key[n]

        do_delete_key_map ==
            IF key_map[k].refcount = 1 THEN
                key_map' = [key_map EXCEPT ![k] = nil]
            ELSE
                UNCHANGED key_map

        on_delete ==
            /\ id_map' = [id_map EXCEPT ![id] = nil]
            /\ do_delete_key_map

        on_dec_ref ==
            /\ id_map' = [id_map EXCEPT ![id].refcount = @ - 1]
            /\ UNCHANGED key_map
    IN
    /\ pc[n] = "Process"
    /\ goto(n, "Terminated")

    /\ IF id_map[id].refcount = 1
        THEN on_delete
        ELSE on_dec_ref

    /\ UNCHANGED last_id
    /\ UNCHANGED <<local_id, local_key>>

--------------------------------------------------------------

StopCond ==
    /\ \A n \in Node: pc[n] \in {"Init", "Process", "Terminated"}

TerminateCond ==
    /\ \A n \in Node: pc[n] = "Terminated"

Terminated ==
    /\ TerminateCond
    /\ UNCHANGED vars

--------------------------------------------------------------

Next ==
    \/ \E n \in Node, k \in Key:
        \/ AddKey(n, k)
    \/ \E n \in Node:
        \/ SetIDMap(n)
        \/ DeleteIDMap(n)
    \/ Terminated

Spec == Init /\ [][Next]_vars

FairSpec == Spec /\ WF_vars(Next)

--------------------------------------------------------------

AlwaysTerminated == []<> TerminateCond

----------------------

KeyMapMatchIDMap ==
    LET
        cond1(k) ==
            key_map[k] # nil =>
                /\ id_map[key_map[k].id] # nil
                /\ id_map[key_map[k].id].key = k

        cond2(id) ==
            id_map[id] # nil =>
                /\ key_map[id_map[id].key] # nil
                /\ key_map[id_map[id].key].id = id
    IN
    StopCond =>
        /\ \A k \in Key: cond1(k)
        /\ \A id \in ID: cond2(id)

--------------------------------------------------------------

Next2 == Next

====

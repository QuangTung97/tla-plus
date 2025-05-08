----- MODULE GenericSync ----
EXTENDS TLC, Naturals, Sequences

CONSTANTS Node, max_action

VARIABLES
    src_db, dst_db, event,
    num_action, next_key, next_val,
    pc

vars == <<
    src_db, dst_db, event,
    num_action, next_key, next_val,
    pc
>>

--------------------------------------------------------------------

Range(f) == {f[x]: x \in DOMAIN f}

MapOf(m, A, B) ==
    /\ DOMAIN m \subseteq A
    /\ Range(m) \subseteq B


MapPut(m, k, v) ==
    LET
        new_dom == (DOMAIN m) \union {k}
    IN
        [x \in new_dom |-> IF x = k THEN v ELSE m[x]]


ASSUME MapPut(<<>>, 1, 4) = <<4>>
ASSUME MapPut(<<3>>, 1, 5) = <<5>>

--------------------------------------------------------------------

ID == 21..29

Value == 31..39

Event == [
    id: ID,
    action: {"Put", "Delete"}
]

--------------------------------------------------------------------

TypeOK ==
    /\ MapOf(src_db, ID, Value)
    /\ MapOf(dst_db, ID, Value)
    /\ event \in Seq(Event)

    /\ num_action \in 0..max_action
    /\ next_key \in (ID \union {20})
    /\ next_val \in (Value \union {30})

    /\ pc \in [Node -> {"Init"}]

Init ==
    /\ src_db = <<>>
    /\ dst_db = <<>>
    /\ event = <<>>

    /\ num_action = 0
    /\ next_key = 20
    /\ next_val = 30

    /\ pc = [n \in Node |-> "Init"]

--------------------------------------------------------------------

sourceUnchanged ==
    /\ UNCHANGED dst_db
    /\ UNCHANGED pc

PutSourceDB ==
    LET
        insert_event(id) ==
            event' = Append(event, [id |-> id, action |-> "Put"])

        insert_new ==
            /\ next_key' = next_key + 1
            /\ src_db' = MapPut(src_db, next_key', next_val')
            /\ insert_event(next_key')

        update_existing ==
            \E id \in DOMAIN src_db:
                /\ src_db' = MapPut(src_db, id, next_val')
                /\ UNCHANGED next_key
                /\ insert_event(id)
    IN
    /\ num_action < max_action
    /\ num_action' = num_action + 1
    /\ next_val' = next_val + 1

    /\ \/ insert_new
       \/ update_existing

    /\ sourceUnchanged

--------------------------------------------------------------------

dstUnchanged ==
    /\ UNCHANGED src_db
    /\ UNCHANGED event
    /\ UNCHANGED <<num_action, next_key, next_val>>

goto(n, l) ==
    pc' = [pc EXCEPT ![n] = l]


NodeLoadStatus(n) ==
    /\ pc[n] = "Init"
    /\ dstUnchanged

--------------------------------------------------------------------

TerminateCond ==
    /\ TRUE

Terminated ==
    /\ TerminateCond
    /\ UNCHANGED vars

Next ==
    \/ PutSourceDB
    \/ \E n \in Node:
        \/ NodeLoadStatus(n)
    \/ Terminated


Spec == Init /\ [][Next]_vars

--------------------------------------------------------------------

====

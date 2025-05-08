----- MODULE GenericSync ----
EXTENDS TLC, Naturals, Sequences

CONSTANTS nil, max_action, max_restart

VARIABLES
    src_db, dst_db, event,
    num_action, next_key, next_val,
    dst_status, last_seq, last_scan_id,
    num_restart

vars == <<
    src_db, dst_db, event,
    num_action, next_key, next_val,
    dst_status, last_seq, last_scan_id,
    num_restart
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

MapDelete(m, k) ==
    LET
        new_dom == (DOMAIN m) \ {k}
    IN
        [x \in new_dom |-> m[x]]

MapDeleteMulti(m, key_set) ==
    LET
        new_dom == (DOMAIN m) \ key_set
    IN
        [x \in new_dom |-> m[x]]

---------------------------

MaxOf(S) == CHOOSE x \in S: (\A y \in S: y <= x)
MinOf(S) == CHOOSE x \in S: (\A y \in S: y >= x)

ASSUME MaxOf({11, 12, 13}) = 13
ASSUME MinOf({11, 12, 13}) = 11

--------------------------------------------------------------------

ID == 21..29

NullID == ID \union {nil}

Value == 31..39

Event == [
    id: ID,
    action: {"Put", "Delete"}
]

ScanStatus == {"Scanning", "Normal"}

NullStatus == ScanStatus \union {nil}

EventSeq == (DOMAIN event) \union {0}

NullSeq == EventSeq \union {nil}

ScanID == ID \union {0, 99}

--------------------------------------------------------------------

TypeOK ==
    /\ MapOf(src_db, ID, Value)
    /\ MapOf(dst_db, ID, Value)
    /\ event \in Seq(Event)

    /\ num_action \in 0..max_action
    /\ next_key \in (ID \union {20})
    /\ next_val \in (Value \union {30})

    /\ dst_status \in ScanStatus
    /\ last_seq \in NullSeq
    /\ last_scan_id \in ScanID

    /\ num_restart \in 0..max_restart

Init ==
    /\ src_db = <<>>
    /\ dst_db = <<>>
    /\ event = <<>>

    /\ num_action = 0
    /\ next_key = 20
    /\ next_val = 30

    /\ dst_status = "Scanning"
    /\ last_seq = nil
    /\ last_scan_id = 0

    /\ num_restart = 0

--------------------------------------------------------------------

sourceUnchanged ==
    /\ UNCHANGED <<dst_db, dst_status, last_seq, last_scan_id>>
    /\ UNCHANGED num_restart


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


DeleteSourceDB ==
    LET
        insert_event(id) ==
            event' = Append(event, [id |-> id, action |-> "Delete"])

        do_delete(id) ==
            /\ src_db' = MapDelete(src_db, id)
            /\ insert_event(id)
    IN
    /\ num_action < max_action
    /\ num_action' = num_action + 1
    /\ \E id \in DOMAIN src_db: do_delete(id)

    /\ UNCHANGED <<next_key, next_val>>
    /\ sourceUnchanged


--------------------------------------------------------------------

dstUnchanged ==
    /\ UNCHANGED src_db
    /\ UNCHANGED event
    /\ UNCHANGED <<num_action, next_key, next_val>>


LoadMaxSeq ==
    /\ dst_status = "Scanning"
    /\ last_seq = nil

    /\ last_seq' = Len(event)

    /\ UNCHANGED <<dst_status, dst_db>>
    /\ UNCHANGED last_scan_id
    /\ UNCHANGED num_restart
    /\ dstUnchanged


ScanNextID ==
    LET
        id_set == {x \in DOMAIN src_db: x > last_scan_id}
        id == MinOf(id_set)

        delete_set == {
            x \in DOMAIN dst_db: x > last_scan_id /\ x <= last_scan_id'}

        new_db == MapPut(dst_db, id, src_db[id])

        scan_next ==
            /\ last_scan_id' = id
            /\ dst_db' = MapDeleteMulti(new_db, delete_set \ {id})
            /\ UNCHANGED dst_status

        finish_scan ==
            /\ last_scan_id' = 99
            /\ dst_status' = "Normal"
            /\ dst_db' = MapDeleteMulti(dst_db, delete_set)
    IN
    /\ dst_status = "Scanning"
    /\ last_seq # nil

    /\ IF id_set # {}
        THEN scan_next
        ELSE finish_scan

    /\ UNCHANGED last_seq
    /\ UNCHANGED num_restart
    /\ dstUnchanged


HandleEvent ==
    LET
        ev == event[last_seq']
        id == ev.id
    IN
    /\ dst_status = "Normal"
    /\ last_seq < Len(event)

    /\ last_seq' = last_seq + 1
    /\ IF ev.action = "Delete" THEN
            dst_db' = MapDelete(dst_db, id)
        ELSE IF id \in DOMAIN src_db THEN
            dst_db' = MapPut(dst_db, id, src_db[id])
        ELSE
            UNCHANGED dst_db

    /\ UNCHANGED last_scan_id
    /\ UNCHANGED dst_status
    /\ UNCHANGED num_restart
    /\ dstUnchanged


RestartScanning ==
    /\ num_restart < max_restart
    /\ num_restart' = num_restart + 1

    /\ dst_status' = "Scanning"
    /\ last_seq' = nil
    /\ last_scan_id' = 0

    /\ UNCHANGED dst_db
    /\ dstUnchanged

--------------------------------------------------------------------

StopCond ==
    /\ dst_status = "Normal"
    /\ last_seq = Len(event)

TerminateCond ==
    /\ StopCond
    /\ num_action = max_action
    /\ num_restart = max_restart

Terminated ==
    /\ TerminateCond
    /\ UNCHANGED vars


Next ==
    \/ PutSourceDB
    \/ DeleteSourceDB

    \/ LoadMaxSeq
    \/ ScanNextID
    \/ HandleEvent
    \/ RestartScanning

    \/ Terminated

Spec == Init /\ [][Next]_vars

FairSpec == Spec /\ WF_vars(Next)

--------------------------------------------------------------------

AlwaysTerminate == []<> TerminateCond


DstAndSourceMatch ==
    StopCond => src_db = dst_db


DstStatusInv ==
    \/ /\ dst_status = "Scanning"
       /\ last_scan_id # 99
    \/ /\ dst_status = "Normal"
       /\ last_seq # nil
       /\ last_scan_id = 99

====

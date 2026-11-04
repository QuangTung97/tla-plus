---- MODULE MultipartWriter ----
EXTENDS TLC, Naturals, Sequences, FiniteSets

CONSTANTS Node, nil, max_num_upload, num_part

VARIABLES
    pc, local_part, local_sema,
    upload_map,
    last_upload_id,
    part_map,
    global_sema

local_vars == <<
    pc, local_part, local_sema
>>

vars == <<
    local_vars,
    upload_map,
    last_upload_id,
    part_map,
    global_sema
>>

--------------------------------------------------------------------

Null(S) == S \union {nil}

--------------------------------------------------------------------

max_upload_id == 10 + max_num_upload
UploadID == 11..max_upload_id
PartNum == 1..num_part

PartID == UploadID \X PartNum

SemaAddr == DOMAIN global_sema

PC == {"Init", "WaitOnSema", "SetWriting", "FinishWrite", "Terminated"}

UploadState == [
    status: {"Init", "Started", "Writing", "Finished"}
]

PartState == [
    sema: SemaAddr,
    consumed: BOOLEAN,
    notified: BOOLEAN
]

SemaData == 0..1

--------------------------------------------------------------------

TypeOK ==
    /\ pc \in [Node -> PC]
    /\ local_part \in [Node -> Null(PartID)]
    /\ local_sema \in [Node -> Null(SemaAddr)]

    /\ last_upload_id \in (UploadID \union {10})
    /\ upload_map \in [UploadID -> Null(UploadState)]

    /\ part_map \in [PartID -> Null(PartState)]
    /\ global_sema \in Seq(SemaData)

Init ==
    /\ pc = [n \in Node |-> "Init"]
    /\ local_part = [n \in Node |-> nil]
    /\ local_sema = [n \in Node |-> nil]

    /\ last_upload_id = 10
    /\ upload_map = [id \in UploadID |-> nil]

    /\ part_map = [p \in PartID |-> nil]
    /\ global_sema = <<>>

--------------------------------------------------------------------

StartUpload ==
    LET
        id == last_upload_id + 1

        state == [
            status |-> "Init"
        ]
    IN
    /\ last_upload_id < max_upload_id
    /\ last_upload_id' = id

    /\ upload_map' = [upload_map EXCEPT ![id] = state]

    /\ UNCHANGED part_map
    /\ UNCHANGED global_sema
    /\ UNCHANGED local_vars

--------------------------------------------------------------------

GetMultipartUrls(id) ==
    LET
        state == upload_map[id]

        base_sema_list == [idx \in 1..num_part |-> 0]
        new_sema_list == [base_sema_list EXCEPT ![1] = 1] \* init first

        last_sema_addr == Len(global_sema)

        update_part_map(x, num, old) ==
            LET
                init_state(notified) == [
                    sema |-> last_sema_addr + num,
                    consumed |-> FALSE,
                    notified |-> notified
                ]
            IN
            IF x = id THEN
                IF num = 1 THEN
                    init_state(TRUE)
                ELSE
                    init_state(FALSE)
            ELSE
                old
    IN
    /\ state # nil
    /\ state.status = "Init"

    /\ upload_map' = [upload_map EXCEPT ![id].status = "Started"]
    /\ part_map' = [p \in PartID |-> update_part_map(p[1], p[2], part_map[p])]

    /\ global_sema' = global_sema \o new_sema_list

    /\ UNCHANGED last_upload_id
    /\ UNCHANGED local_vars

--------------------------------------------------------------------

set_local(n, var, x) ==
    var' = [var EXCEPT ![n] = x]

goto(n, l) ==
    set_local(n, pc, l)

--------------------------------------------------------------------

GetPartWriter(n, p) ==
    LET
        state == part_map[p]
    IN
    /\ pc[n] = "Init"
    /\ state # nil
    /\ ~state.consumed

    /\ goto(n, "WaitOnSema")
    /\ part_map' = [part_map EXCEPT ![p].consumed = TRUE]

    /\ set_local(n, local_part, p)
    /\ set_local(n, local_sema, state.sema)

    /\ UNCHANGED upload_map
    /\ UNCHANGED global_sema
    /\ UNCHANGED last_upload_id

--------------------------------------------------------------------

WaitOnSema(n) ==
    LET
        sem == local_sema[n]
    IN
    /\ pc[n] = "WaitOnSema"
    /\ global_sema[sem] > 0

    /\ global_sema' = [global_sema EXCEPT ![sem] = @ - 1]
    /\ goto(n, "SetWriting")

    /\ UNCHANGED local_part
    /\ UNCHANGED local_sema
    /\ UNCHANGED last_upload_id
    /\ UNCHANGED upload_map
    /\ UNCHANGED part_map

--------------------------------------------------------------------

SetWriting(n) ==
    LET
        p == local_part[n]
        id == p[1]
    IN
    /\ pc[n] = "SetWriting"

    /\ upload_map' = [upload_map EXCEPT ![id].status = "Writing"]
    /\ goto(n, "FinishWrite")

    /\ UNCHANGED part_map
    /\ UNCHANGED <<local_part, local_sema>>
    /\ UNCHANGED global_sema
    /\ UNCHANGED last_upload_id

--------------------------------------------------------------------

FinishWrite(n) ==
    LET
        p == local_part[n]
        id == p[1]
        num == p[2]

        next_num == num + 1
        next_part == <<id, next_num>>
        next_sem == part_map[next_part].sema

        notify_next ==
            IF next_num \in PartNum THEN
                /\ part_map' = [part_map EXCEPT ![next_part].notified = TRUE]
                /\ global_sema' = [global_sema EXCEPT ![next_sem] = @ + 1]
            ELSE
                /\ UNCHANGED global_sema
                /\ UNCHANGED part_map
    IN
    /\ pc[n] = "FinishWrite"

    /\ upload_map' = [upload_map EXCEPT ![id].status = "Started"]
    /\ notify_next
    /\ goto(n, "Terminated")

    /\ set_local(n, local_part, nil)
    /\ set_local(n, local_sema, nil)

    /\ UNCHANGED last_upload_id

--------------------------------------------------------------------

TerminateCond ==
    /\ last_upload_id = max_upload_id
    /\ \A n \in Node:
        pc[n] = "Terminated"
    /\ \A id \in UploadID: upload_map[id] = nil
    /\ \A p \in PartID: part_map[p] = nil

Terminated ==
    /\ TerminateCond
    /\ UNCHANGED vars

--------------------------------------------------------------------

Next ==
    \/ StartUpload
    \/ \E id \in UploadID:
        \/ GetMultipartUrls(id)
    \/ \E n \in Node, p \in PartID:
        \/ GetPartWriter(n, p)
    \/ \E n \in Node:
        \/ WaitOnSema(n)
        \/ SetWriting(n)
        \/ FinishWrite(n)
    \/ Terminated

Spec == Init /\ [][Next]_vars

--------------------------------------------------------------------

====

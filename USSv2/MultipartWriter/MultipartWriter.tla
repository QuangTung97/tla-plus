---- MODULE MultipartWriter ----
EXTENDS TLC, Naturals, Sequences, FiniteSets

CONSTANTS Node, nil, max_num_upload, num_part

VARIABLES
    pc, local_sema,
    upload_map,
    last_upload_id,
    part_map,
    global_sema

local_vars == <<
    pc, local_sema
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

PC == {"Init", "WaitOnSema", "Terminated"}

UploadState == [
    status: {"Init", "Started", "Finished"}
]

--------------------------------------------------------------------

TypeOK ==
    /\ pc \in [Node -> PC]
    /\ local_sema \in [Node -> Null(SemaAddr)]

    /\ last_upload_id \in (UploadID \union {10})
    /\ upload_map \in [UploadID -> Null(UploadState)]

    /\ part_map \in [PartID -> Null(SemaAddr)]
    /\ global_sema \in Seq(Nat)

Init ==
    /\ pc = [n \in Node |-> "Init"]
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

        new_sema_list == [idx \in 1..num_part |-> 0]

        last_sema_addr == Len(global_sema)

        update_part_map(x, num, old) ==
            IF x = id THEN
                last_sema_addr + num
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
        sem == part_map[p]
    IN
    /\ pc[n] = "Init"
    /\ sem # nil

    /\ goto(n, "WaitOnSema")
    /\ part_map' = [part_map EXCEPT ![p] = nil]
    /\ set_local(n, local_sema, sem)

    /\ UNCHANGED upload_map
    /\ UNCHANGED global_sema
    /\ UNCHANGED last_upload_id

--------------------------------------------------------------------

TerminateCond ==
    /\ FALSE

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
    \/ Terminated

Spec == Init /\ [][Next]_vars

--------------------------------------------------------------------

====

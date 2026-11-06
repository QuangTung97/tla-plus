---- MODULE MultipartWriter ----
EXTENDS TLC, Naturals, Sequences, FiniteSets

CONSTANTS Node, nil, max_num_upload, num_part

VARIABLES
    pc, local_part, local_sema,
    upload_map,
    last_upload_id,
    part_map,
    global_sema,
    callback_pc

local_vars == <<
    pc, local_part, local_sema
>>

vars == <<
    local_vars,
    upload_map,
    last_upload_id,
    part_map,
    global_sema,
    callback_pc
>>

--------------------------------------------------------------------

Null(S) == S \union {nil}

--------------------------------------------------------------------

max_upload_id == 10 + max_num_upload
UploadID == 11..max_upload_id
PartNum == 1..num_part

PartID == UploadID \X PartNum

SemaAddr == DOMAIN global_sema

PC == {
    "Init", "WaitOnSema",
    "SetWriting", "FinishWrite",
    "WaitOnFinishSema",
    "Terminated"
}

UploadState == [
    status: {"Init", "Started", "Finished"},
    pending: SUBSET PartNum,
    finish_sema: SemaAddr,
    finish_consumed: BOOLEAN,
    writing: 0..1
]

PartState == [
    sema: SemaAddr,
    consumed: BOOLEAN,
    notified: BOOLEAN
]

SemaData == 0..1

CallbackPC == {"Init", "Terminated"}

--------------------------------------------------------------------

TypeOK ==
    /\ pc \in [Node -> PC]
    /\ local_part \in [Node -> Null(PartID)]
    /\ local_sema \in [Node -> Null(SemaAddr)]

    /\ last_upload_id \in (UploadID \union {10})
    /\ upload_map \in [UploadID -> Null(UploadState)]

    /\ part_map \in [PartID -> Null(PartState)]
    /\ global_sema \in Seq(SemaData)

    /\ callback_pc \in [UploadID -> Null(CallbackPC)]

Init ==
    /\ pc = [n \in Node |-> "Init"]
    /\ local_part = [n \in Node |-> nil]
    /\ local_sema = [n \in Node |-> nil]

    /\ last_upload_id = 10
    /\ upload_map = [id \in UploadID |-> nil]

    /\ part_map = [p \in PartID |-> nil]
    /\ global_sema = <<>>

    /\ callback_pc = [id \in UploadID |-> nil]

--------------------------------------------------------------------

StartUpload ==
    LET
        id == last_upload_id + 1

        sem == Len(global_sema) + 1

        state == [
            status |-> "Init",
            pending |-> {},
            finish_sema |-> sem,
            finish_consumed |-> FALSE,
            writing |-> 0
        ]
    IN
    /\ last_upload_id < max_upload_id
    /\ last_upload_id' = id

    /\ global_sema' = Append(global_sema, 0)
    /\ upload_map' = [upload_map EXCEPT ![id] = state]
    /\ callback_pc' = [callback_pc EXCEPT ![id] = "Init"]

    /\ UNCHANGED part_map
    /\ UNCHANGED local_vars

--------------------------------------------------------------------

notify_sema_list(input_global_sema, sem_set) ==
    LET
        update_sema(sem, old) ==
            IF sem \in sem_set
                THEN old + 1
                ELSE old
    IN
    [
        sem \in DOMAIN input_global_sema |->
            update_sema(sem, input_global_sema[sem])
    ]

---------------------------

put_map(input_map, key_set, update_fn(_, _)) ==
    LET
        do_update(k, old) ==
            IF k \in key_set
                THEN update_fn(k, old)
                ELSE old
    IN
    [k \in DOMAIN input_map |-> do_update(k, input_map[k])]

--------------------------------------------------------------------

GetMultipartUrls(id) ==
    LET
        state == upload_map[id]

        append_sema_list == [num \in PartNum |-> 0]
        appended_global_sema == global_sema \o append_sema_list

        first_sem == Len(global_sema) + 1
        new_global_sema == notify_sema_list(appended_global_sema, {first_sem})

        part_id_set == {id} \X PartNum

        init_part_state(p, _old) == [
            sema |-> Len(global_sema) + p[2],
            consumed |-> FALSE,
            notified |-> FALSE
        ]

        base_part_map == put_map(part_map, part_id_set, init_part_state)

        set_notified_fn(p, old) == [old EXCEPT !.notified = TRUE]

        first_part_id == <<id, 1>>
        new_part_map == put_map(base_part_map, {first_part_id}, set_notified_fn)
    IN
    /\ state # nil
    /\ state.status = "Init"

    /\ upload_map' = [upload_map EXCEPT
            ![id].status = "Started",
            ![id].pending = PartNum
        ]
    /\ part_map' = new_part_map
    /\ global_sema' = new_global_sema

    /\ UNCHANGED last_upload_id
    /\ UNCHANGED callback_pc
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
    /\ UNCHANGED callback_pc
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
    /\ UNCHANGED callback_pc
    /\ UNCHANGED part_map

--------------------------------------------------------------------

SetWriting(n) ==
    LET
        p == local_part[n]
        id == p[1]
    IN
    /\ pc[n] = "SetWriting"

    /\ upload_map' = [upload_map EXCEPT ![id].writing = @ + 1]
    /\ goto(n, "FinishWrite")

    /\ UNCHANGED part_map
    /\ UNCHANGED <<local_part, local_sema>>
    /\ UNCHANGED global_sema
    /\ UNCHANGED last_upload_id
    /\ UNCHANGED callback_pc

--------------------------------------------------------------------

FinishWrite(n) ==
    LET
        p == local_part[n]
        id == p[1]
        num == p[2]

        next_num == num + 1
        next_part == <<id, next_num>>
        next_sem == part_map[next_part].sema

        part_map_deleted == [part_map EXCEPT ![p] = nil]

        notify_next ==
            IF next_num \in PartNum THEN
                /\ part_map' = [part_map_deleted EXCEPT
                        ![next_part].notified = TRUE
                    ]
                /\ global_sema' = [global_sema EXCEPT ![next_sem] = @ + 1]
            ELSE
                /\ part_map' = part_map_deleted
                /\ UNCHANGED global_sema
    IN
    /\ pc[n] = "FinishWrite"

    /\ upload_map' = [upload_map EXCEPT
            ![id].pending = @ \ {num},
            ![id].writing = @ - 1
        ]
    /\ notify_next
    /\ goto(n, "Terminated")

    /\ set_local(n, local_part, nil)
    /\ set_local(n, local_sema, nil)

    /\ UNCHANGED last_upload_id
    /\ UNCHANGED callback_pc

--------------------------------------------------------------------

CallbackComplete(id) ==
    LET
        finish_sem == upload_map[id].finish_sema
    IN
    /\ callback_pc[id] = "Init"
    /\ upload_map[id].pending = {}
    /\ upload_map[id].status = "Started"

    /\ callback_pc' = [callback_pc EXCEPT ![id] = "Terminated"]
    /\ upload_map' = [upload_map EXCEPT ![id].status = "Finished"]
    /\ global_sema' = [global_sema EXCEPT ![finish_sem] = 1]

    /\ UNCHANGED part_map
    /\ UNCHANGED local_vars
    /\ UNCHANGED last_upload_id

--------------------------------------------------------------------

StartWaitFinish(n, id) ==
    LET
        state == upload_map[id]
    IN
    /\ pc[n] = "Init"
    /\ state # nil
    /\ ~state.finish_consumed

    /\ goto(n, "WaitOnFinishSema")
    /\ set_local(n, local_sema, state.finish_sema)
    /\ set_local(n, local_part, <<id, 1>>)
    /\ upload_map' = [upload_map EXCEPT ![id].finish_consumed = TRUE]

    /\ UNCHANGED part_map
    /\ UNCHANGED callback_pc
    /\ UNCHANGED global_sema
    /\ UNCHANGED last_upload_id

--------------------------------------------------------------------

WaitOnFinishSema(n) ==
    LET
        id == local_part[n][1]
        sem == local_sema[n]
    IN
    /\ pc[n] = "WaitOnFinishSema"
    /\ global_sema[sem] = 1

    /\ upload_map' = [upload_map EXCEPT ![id] = nil]
    /\ goto(n, "Terminated")
    /\ set_local(n, local_sema, nil)
    /\ set_local(n, local_part, nil)

    /\ UNCHANGED global_sema
    /\ UNCHANGED last_upload_id
    /\ UNCHANGED part_map
    /\ UNCHANGED callback_pc

--------------------------------------------------------------------

TerminateCond ==
    /\ \A n \in Node:
        pc[n] = "Terminated"
    /\ \A id \in UploadID:
        /\ upload_map[id] = nil
        /\ callback_pc[id] \in {nil, "Terminated"}
    /\ \A p \in PartID: part_map[p] = nil

Terminated ==
    /\ TerminateCond
    /\ UNCHANGED vars

--------------------------------------------------------------------

Next ==
    \/ StartUpload
    \/ \E id \in UploadID:
        \/ GetMultipartUrls(id)
        \/ CallbackComplete(id)
    \/ \E n \in Node, p \in PartID:
        \/ GetPartWriter(n, p)
    \/ \E n \in Node:
        \/ WaitOnSema(n)
        \/ SetWriting(n)
        \/ FinishWrite(n)
        \/ WaitOnFinishSema(n)
    \/ \E n \in Node, id \in UploadID:
        \/ StartWaitFinish(n, id)
    \/ Terminated

Spec == Init /\ [][Next]_vars

--------------------------------------------------------------------

UploadPendingMatchPartMap ==
    LET
        in_pending(p) ==
            /\ upload_map[p[1]] # nil
            /\ p[2] \in upload_map[p[1]].pending
    IN
    \A p \in PartID:
        part_map[p] # nil <=> in_pending(p)

--------------------------------------------------------------------

====

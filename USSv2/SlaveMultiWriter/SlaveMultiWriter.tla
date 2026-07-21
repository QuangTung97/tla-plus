---- MODULE SlaveMultiWriter ----
EXTENDS TLC, Naturals, Sequences

CONSTANTS Node, Writer, nil

VARIABLES
    pc, status, pending_writers,
    write_version, generation, events,
    local_writer, local_write_version,
    web_gen, web_write_version

slave_vars == <<
    status, pending_writers,
    write_version, generation
>>

local_vars == <<pc, local_writer, local_write_version>>

web_vars == <<web_gen, web_write_version>>

vars == <<
    slave_vars,
    events,
    local_vars,
    web_vars
>>

------------------------------------------------------------

Null(S) == S \union {nil}

SlaveStatus == {"Init", "Writing", "WriteCompleted", "WriteTimeout", "Finished"}

PC == {"Init", "Writing", "TriggerAsync", "Terminated"}

WriteVersion == 20..29

Generation == 30..39

Event == [
    version: Null(WriteVersion)
]

------------------------------------------------------------

TypeOK ==
    /\ status \in SlaveStatus
    /\ pending_writers \subseteq Writer
    /\ write_version \in WriteVersion
    /\ generation \in Generation

    /\ events \in Seq(Event)

    /\ pc \in [Node -> PC]
    /\ local_writer \in [Node -> Null(Writer)]
    /\ local_write_version \in [Node -> Null(WriteVersion)]

    /\ web_gen \in Generation
    /\ web_write_version \in Null(WriteVersion)

Init ==
    /\ status = "Init"
    /\ pending_writers = {}
    /\ write_version = 20
    /\ generation = 30

    /\ events = <<>>

    /\ pc = [n \in Node |-> "Init"]
    /\ local_writer = [n \in Node |-> nil]
    /\ local_write_version = [n \in Node |-> nil]

    /\ web_gen = 30
    /\ web_write_version = nil

------------------------------------------------------------

goto(n, l) ==
    pc' = [pc EXCEPT ![n] = l]

set_local(n, var, x) ==
    var' = [var EXCEPT ![n] = x]

--------------------------------

Write(n, w) ==
    LET
        update_pending ==
            pending_writers' = pending_writers \union {w}
    IN
    /\ pc[n] = "Init"
    /\ status' = "Writing"
    /\ goto(n, "Writing")
    /\ write_version' = write_version + 1
    /\ generation' = web_gen
    /\ update_pending
    /\ set_local(n, local_writer, w)

    /\ UNCHANGED local_write_version
    /\ UNCHANGED web_vars
    /\ UNCHANGED events

------------------------------------------------------------

WriteComplete(n) ==
    LET
        w == local_writer[n]

        allow_cond ==
            /\ status = "Writing"
            /\ w \in pending_writers

        new_pending == pending_writers \ {w}

        on_write_completed ==
            /\ status' = "WriteCompleted"
            /\ goto(n, "Terminated")
            /\ UNCHANGED local_write_version

        on_run_background ==
            /\ UNCHANGED status
            /\ goto(n, "TriggerAsync")
            /\ set_local(n, local_write_version, write_version)

        update_status ==
            IF new_pending = {}
                THEN on_write_completed
                ELSE on_run_background

        on_normal ==
            /\ update_status
            /\ pending_writers' = new_pending

        on_nop ==
            /\ goto(n, "Terminated")
            /\ UNCHANGED status
            /\ UNCHANGED pending_writers
            /\ UNCHANGED local_write_version
    IN
    /\ pc[n] = "Writing"
    /\ IF allow_cond
        THEN on_normal
        ELSE on_nop

    /\ UNCHANGED local_writer
    /\ UNCHANGED generation
    /\ UNCHANGED web_vars
    /\ UNCHANGED events
    /\ UNCHANGED write_version

------------------------------------------------------------

TriggerAsync(n) ==
    LET
        e == [
            version |-> nil
        ]

        normal_cond ==
            /\ status = "Writing"
            /\ write_version = local_write_version[n]

        on_normal ==
            /\ events' = Append(events, e)

        on_nop ==
            /\ UNCHANGED events
    IN
    /\ pc[n] = "TriggerAsync"
    /\ goto(n, "Terminated")

    /\ IF normal_cond
        THEN on_normal
        ELSE on_nop

    /\ UNCHANGED local_writer
    /\ UNCHANGED local_write_version
    /\ UNCHANGED status
    /\ UNCHANGED generation
    /\ UNCHANGED write_version
    /\ UNCHANGED pending_writers
    /\ UNCHANGED web_vars

------------------------------------------------------------

PushToWeb ==
    LET
        e == [
            version |-> write_version
        ]
    IN
    /\ status \in {"WriteCompleted", "WriteTimeout"}
    /\ status' = "Finished"
    /\ events' = Append(events, e)

    /\ UNCHANGED write_version
    /\ UNCHANGED pending_writers
    /\ UNCHANGED generation
    /\ UNCHANGED local_vars
    /\ UNCHANGED web_vars

------------------------------------------------------------

WriteTimeout ==
    /\ status \in {"Writing"}

    /\ status' = "WriteTimeout"
    /\ pending_writers' = {}

    /\ UNCHANGED events
    /\ UNCHANGED write_version
    /\ UNCHANGED generation
    /\ UNCHANGED local_vars
    /\ UNCHANGED web_vars

------------------------------------------------------------

ConsumeEvent ==
    LET
        e == events[1]

        update_version ==
            IF e.version # nil THEN
                web_write_version' = e.version
            ELSE
                UNCHANGED web_write_version
    IN
    /\ Len(events) > 0

    /\ events' = Tail(events)
    /\ update_version

    /\ UNCHANGED web_gen
    /\ UNCHANGED local_vars
    /\ UNCHANGED slave_vars

------------------------------------------------------------

TerminateCond ==
    /\ \A n \in Node: pc[n] = "Terminated"
    /\ status = "Finished"
    /\ events = <<>>

Terminated ==
    /\ TerminateCond
    /\ UNCHANGED vars

------------------------------------------------------------

Next ==
    \/ \E n \in Node, w \in Writer:
        \/ Write(n, w)
    \/ \E n \in Node:
        \/ WriteComplete(n)
        \/ TriggerAsync(n)
    \/ PushToWeb
    \/ WriteTimeout
    \/ ConsumeEvent
    \/ Terminated

Spec == Init /\ [][Next]_vars

------------------------------------------------------------

OnlyWritingHasPendingWriters ==
    pending_writers # {} => status = "Writing"


webWriteVersionAction ==
    IF web_write_version = nil THEN
        web_write_version' # nil
    ELSE
        /\ web_write_version' # nil
        /\ web_write_version' > web_write_version

WebWriteVersionProperty ==
    [][webWriteVersionAction]_web_write_version


====

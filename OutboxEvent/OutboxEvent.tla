------ MODULE OutboxEvent ----
EXTENDS TLC, Sequences, Naturals, FiniteSets

TruncateSeq(s, n) ==
    IF Len(s) < n
        THEN s
        ELSE SubSeq(s, 1, n)

ASSUME TruncateSeq(<<11, 12, 13>>, 2) = <<11, 12>>
ASSUME TruncateSeq(<<11, 12, 13>>, 4) = <<11, 12, 13>>

MinOf(s) == CHOOSE x \in s: (\A y \in s: y >= x)

ASSUME MinOf({21, 22, 23}) = 21

--------------------------------------------------------

CONSTANTS Node, nil, max_event

VARIABLES events, pc, local_null_events, local_last_seq

local_vars == <<pc, local_null_events, local_last_seq>>

vars == <<events, local_vars>>

--------------------------------------------------------

StartEventID == 30

EventID == StartEventID..39

EventSeq == 20..29
NullSeq == EventSeq \union {nil}

Event == [
    id: EventID,
    seq: NullSeq
]

PC == {"Init", "GetLastSeq", "SetSeqNum"}

last_event_id ==
    IF events = <<>>
        THEN StartEventID
        ELSE events[Len(events)].id

--------------------------------------------------------

TypeOK ==
    /\ events \in Seq(Event)
    /\ pc \in [Node -> PC]
    /\ local_null_events \in [Node -> Seq(Event)]
    /\ local_last_seq \in [Node -> NullSeq]

Init ==
    /\ events = <<>>
    /\ pc = [n \in Node |-> "Init"]
    /\ local_null_events = [n \in Node |-> <<>>]
    /\ local_last_seq = [n \in Node |-> nil]

--------------------------------------------------------

NewEvent ==
    LET
        ev == [
            id |-> last_event_id + 1,
            seq |-> nil
        ]
    IN
    /\ last_event_id < StartEventID + max_event
    /\ events' = Append(events, ev)
    /\ UNCHANGED local_vars

--------------------------------------------------------

goto(n, l) ==
    pc' = [pc EXCEPT ![n] = l]


GetNullEvents(n) ==
    LET
        filter_fn(e) == e.seq = nil
        tmp == SelectSeq(events, filter_fn)
        null_events == tmp
    IN
    /\ pc[n] = "Init"
    /\ Len(null_events) > 0

    /\ goto(n, "GetLastSeq")
    /\ local_null_events' = [local_null_events EXCEPT ![n] = null_events]

    /\ UNCHANGED local_last_seq
    /\ UNCHANGED events


GetLastSeq(n) ==
    LET
        filter_fn(e) == e.seq # nil
        tmp == SelectSeq(events, filter_fn)

        last_seq ==
            IF Len(tmp) = 0
                THEN 20
                ELSE tmp[Len(tmp)].seq
    IN
    /\ pc[n] = "GetLastSeq"
    /\ goto(n, "SetSeqNum")

    /\ local_last_seq' = [local_last_seq EXCEPT ![n] = last_seq]

    /\ UNCHANGED local_null_events
    /\ UNCHANGED events

-------------------

RECURSIVE updateSeqByNullEvents(_, _, _)

updateSeqByNullEvents(input_events, null_events, next_seq) ==
    LET
        first == null_events[1]

        update_fn(ev) ==
            IF ev.id = first.id
                THEN [ev EXCEPT !.seq = next_seq]
                ELSE ev

        updated == [idx \in DOMAIN input_events |->
                update_fn(input_events[idx])
            ]
    IN
        IF null_events = <<>>
            THEN input_events
            ELSE updateSeqByNullEvents(updated, Tail(null_events), next_seq + 1)

-------------------

withNoSeqDuplication(input_events) ==
    LET
        seq_set == {input_events[idx].seq: idx \in DOMAIN input_events}
        non_null == {s \in seq_set: s # nil}

        filter_fn(e) == e.seq # nil
        non_null_seq == SelectSeq(input_events, filter_fn)
    IN
        Cardinality(non_null) = Len(non_null_seq)

-------------------

SetSeqNum(n) ==
    LET
        list == local_null_events[n]
        last_seq == local_last_seq[n]

        updated_events == updateSeqByNullEvents(events, list, last_seq + 1)
    IN
    /\ pc[n] = "SetSeqNum"
    /\ goto(n, "Init")

    /\ IF withNoSeqDuplication(updated_events)
        THEN events' = updated_events
        ELSE UNCHANGED events

    /\ local_last_seq' = [local_last_seq EXCEPT ![n] = nil]
    /\ local_null_events' = [local_null_events EXCEPT ![n] = <<>>]

--------------------------------------------------------

TerminateCond ==
    /\ last_event_id >= StartEventID + max_event
    /\ \A n \in Node:
        /\ pc[n] = "Init"
        /\ ~(ENABLED GetNullEvents(n))

Terminated ==
    /\ TerminateCond
    /\ UNCHANGED vars

Next ==
    \/ NewEvent
    \/ \E n \in Node:
        \/ GetNullEvents(n)
        \/ GetLastSeq(n)
        \/ SetSeqNum(n)
    \/ Terminated


Spec == Init /\ [][Next]_vars

--------------------------------------------------------

NoDuplicatedSeq ==
    withNoSeqDuplication(events)


NoMissingSeq ==
    LET
        filter_fn(e) == e.seq # nil
        non_null == SelectSeq(events, filter_fn)
    IN
        \A idx \in DOMAIN non_null: non_null[idx].seq = 20 + idx


WhenTerminateInv ==
    LET
        cond ==
            \A idx \in DOMAIN events: events[idx].seq # nil
    IN
        TerminateCond => cond

====

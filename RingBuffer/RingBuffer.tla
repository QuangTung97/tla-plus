------ MODULE RingBuffer ----
EXTENDS TLC, Naturals, Sequences

CONSTANTS Node, nil, infinity, buff_len

VARIABLES
    buffer, next_seq, pc,
    current_val, local_seq, local_val, god_log,
    consume_pc, consume_seq, consume_log, notify_seq

node_vars == <<
    next_seq, pc,
    current_val, local_seq, local_val, god_log, notify_seq
>>

consume_vars == <<consume_pc, consume_seq, consume_log>>

vars == <<
    buffer,
    node_vars,
    consume_vars
>>

---------------------------------------------------------

Sequence == 0..15
NullSeq == Sequence \union {nil}

Value == 20..29
NullValue == Value \union {nil}

Item == [
    next: Sequence \union {infinity},
    data: NullValue
]

init_item == [
    next |-> 0,
    data |-> nil
]

PC == {
    "Init", "LoadConsumeSeq",
    "WriteData", "MarkFinish", "NotifyConsumer",
    "Terminated"
}

---------------------------------------------------------

TypeOK ==
    /\ buffer \in Seq(Item)
    /\ next_seq \in Sequence

    /\ pc \in [Node -> PC]
    /\ current_val \in Value
    /\ local_seq \in [Node -> NullSeq]
    /\ local_val \in [Node -> NullValue]

    /\ god_log \in Seq(Value)

    /\ consume_pc \in {"Init", "WaitNotify", "ReadData"}
    /\ consume_seq \in Sequence
    /\ consume_log \in Seq(Value)
    /\ notify_seq \in Sequence

Init ==
    /\ buffer = [x \in 1..buff_len |-> init_item]
    /\ next_seq = 0

    /\ pc = [n \in Node |-> "Init"]
    /\ current_val = 20
    /\ local_seq = [n \in Node |-> nil]
    /\ local_val = [n \in Node |-> nil]

    /\ god_log = <<>>

    /\ consume_pc = "Init"
    /\ consume_seq = 0
    /\ consume_log = <<>>
    /\ notify_seq = 0

---------------------------------------------------------

nodeUnchanged ==
    /\ UNCHANGED consume_vars

goto(n, l) ==
    pc' = [pc EXCEPT ![n] = l]

setLocal(n, var, x) ==
    var' = [var EXCEPT ![n] = x]

StartSend(n) ==
    /\ pc[n] = "Init"
    /\ goto(n, "LoadConsumeSeq")

    /\ next_seq' = next_seq + 1
    /\ current_val' = current_val + 1
    /\ setLocal(n, local_seq, next_seq)
    /\ setLocal(n, local_val, current_val')
    /\ god_log' = Append(god_log, current_val')

    /\ UNCHANGED buffer
    /\ UNCHANGED notify_seq
    /\ nodeUnchanged

-----------------------

computeBufferPos(seq) == (seq % buff_len) + 1

unchangedLocal ==
    /\ nodeUnchanged
    /\ UNCHANGED <<local_seq, local_val>>
    /\ UNCHANGED current_val
    /\ UNCHANGED next_seq
    /\ UNCHANGED god_log


LoadConsumeSeq(n) ==
    /\ pc[n] = "LoadConsumeSeq"
    /\ local_seq[n] < consume_seq + buff_len

    /\ goto(n, "WriteData")

    /\ UNCHANGED buffer
    /\ UNCHANGED notify_seq
    /\ unchangedLocal

-----------------------

WriteData(n) ==
    LET
        pos == computeBufferPos(local_seq[n])
    IN
    /\ pc[n] = "WriteData"
    /\ goto(n, "MarkFinish")

    /\ buffer' = [buffer EXCEPT ![pos].data = local_val[n]]

    /\ UNCHANGED notify_seq
    /\ unchangedLocal

-----------------------

MarkFinish(n) ==
    LET
        pos == computeBufferPos(local_seq[n])
        item == buffer[pos]
    IN
    /\ pc[n] = "MarkFinish"

    /\ buffer' = [buffer EXCEPT ![pos].next = local_seq[n] + 1]
    /\ IF item.next = infinity
        THEN goto(n, "NotifyConsumer")
        ELSE goto(n, "Terminated")

    /\ UNCHANGED notify_seq
    /\ unchangedLocal

-----------------------

NotifyConsumer(n) ==
    /\ pc[n] = "NotifyConsumer"
    /\ goto(n, "Terminated")

    /\ notify_seq' = local_seq[n] + 1

    /\ UNCHANGED buffer
    /\ unchangedLocal

---------------------------------------------------------

StartConsume ==
    LET
        pos == computeBufferPos(consume_seq)
        item == buffer[pos]

        when_wait ==
            /\ consume_pc' = "WaitNotify"
            /\ buffer' = [buffer EXCEPT ![pos].next = infinity]

        when_normal ==
            /\ consume_pc' = "ReadData"
            /\ UNCHANGED buffer
    IN
    /\ consume_pc = "Init"
    /\ IF item.next = 0
        THEN when_wait
        ELSE when_normal

    /\ UNCHANGED consume_seq
    /\ UNCHANGED consume_log
    /\ UNCHANGED node_vars

-----------------------

WaitNotify ==
    /\ consume_pc = "WaitNotify"
    /\ consume_seq < notify_seq

    /\ consume_pc' = "Init"

    /\ UNCHANGED consume_seq
    /\ UNCHANGED consume_log
    /\ UNCHANGED buffer
    /\ UNCHANGED node_vars

-----------------------

ReadData ==
    LET
        pos == computeBufferPos(consume_seq)
        item == buffer[pos]
    IN
    /\ consume_pc = "ReadData"
    /\ consume_pc' = "Init"

    /\ consume_seq' = item.next
    /\ buffer' = [buffer EXCEPT
            ![pos].next = 0,
            ![pos].data = nil
        ]
    /\ consume_log' = Append(consume_log, item.data)

    /\ UNCHANGED node_vars

---------------------------------------------------------

TerminateCond ==
    /\ \A n \in Node:
        pc[n] = "Terminated"
    /\ consume_pc = "WaitNotify"
    /\ Len(consume_log) = Len(god_log)

Terminated ==
    /\ TerminateCond
    /\ UNCHANGED vars


Next ==
    \/ \E n \in Node:
        \/ StartSend(n)
        \/ LoadConsumeSeq(n)
        \/ WriteData(n)
        \/ MarkFinish(n)
        \/ NotifyConsumer(n)
    \/ StartConsume
    \/ WaitNotify
    \/ ReadData
    \/ Terminated

Spec == Init /\ [][Next]_vars

FairSpec == Spec /\ WF_vars(Next)

---------------------------------------------------------

AlwaysTerminated == []<>TerminateCond

BufferSizeInv == Len(buffer) = buff_len

GodLogInv ==
    /\ Len(consume_log) <= Len(god_log)
    /\ consume_log = SubSeq(god_log, 1, Len(consume_log))

====

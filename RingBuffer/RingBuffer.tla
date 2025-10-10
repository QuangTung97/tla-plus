------ MODULE RingBuffer ----
EXTENDS TLC, Naturals, Sequences

CONSTANTS Node, nil, buff_len

VARIABLES
    buffer, next_seq, pc,
    current_val, local_seq, local_val, god_log

vars == <<
    buffer, next_seq, pc,
    current_val, local_seq, local_val, god_log
>>

---------------------------------------------------------

Sequence == 0..15
NullSeq == Sequence \union {nil}

Value == 20..29
NullValue == Value \union {nil}

Item == [
    next: Sequence,
    data: NullValue
]

init_item == [
    next |-> 0,
    data |-> nil
]

PC == {"Init", "WriteData", "MarkFinish", "Terminated"}

---------------------------------------------------------

TypeOK ==
    /\ buffer \in Seq(Item)
    /\ next_seq \in Sequence

    /\ pc \in [Node -> PC]
    /\ current_val \in Value
    /\ local_seq \in [Node -> NullSeq]
    /\ local_val \in [Node -> NullValue]

    /\ god_log \in Seq(Value)

Init ==
    /\ buffer = [x \in 1..buff_len |-> init_item]
    /\ next_seq = 0

    /\ pc = [n \in Node |-> "Init"]
    /\ current_val = 20
    /\ local_seq = [n \in Node |-> nil]
    /\ local_val = [n \in Node |-> nil]

    /\ god_log = <<>>

---------------------------------------------------------

goto(n, l) ==
    pc' = [pc EXCEPT ![n] = l]

setLocal(n, var, x) ==
    var' = [var EXCEPT ![n] = x]

StartSend(n) ==
    /\ pc[n] = "Init"
    /\ goto(n, "WriteData")

    /\ next_seq' = next_seq + 1
    /\ current_val' = current_val + 1
    /\ setLocal(n, local_seq, next_seq)
    /\ setLocal(n, local_val, current_val')
    /\ god_log' = Append(god_log, current_val')

    /\ UNCHANGED buffer

-----------------------

computeBufferPos(seq) == (seq % buff_len) + 1

unchangedLocal ==
    /\ UNCHANGED <<local_seq, local_val>>
    /\ UNCHANGED current_val
    /\ UNCHANGED next_seq
    /\ UNCHANGED god_log

WriteData(n) ==
    LET
        pos == computeBufferPos(local_seq[n])
    IN
    /\ pc[n] = "WriteData"
    /\ goto(n, "MarkFinish")

    /\ buffer' = [buffer EXCEPT ![pos].data = local_val[n]]

    /\ unchangedLocal

---------------------------------------------------------

TerminateCond ==
    /\ \A n \in Node:
        pc[n] = "Terminated"

Terminated ==
    /\ TerminateCond
    /\ UNCHANGED vars


Next ==
    \/ \E n \in Node:
        \/ StartSend(n)
        \/ WriteData(n)
    \/ Terminated

Spec == Init /\ [][Next]_vars

---------------------------------------------------------

BufferSizeInv == Len(buffer) = buff_len

====

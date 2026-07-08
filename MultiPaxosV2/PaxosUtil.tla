---- MODULE PaxosUtil ----
EXTENDS TLC, Naturals, FiniteSets, Sequences

CONSTANTS nil, infinity

-----------------------

QuorumOf(S) ==
    LET
        power_set == SUBSET S
        len == Cardinality(S)
        n == (len \div 2) + 1
    IN
        {x \in power_set: Cardinality(x) = n}

ASSUME QuorumOf({11, 12, 13}) = {{11, 12}, {12, 13}, {13, 11}}
ASSUME QuorumOf({11, 12}) = {{11, 12}}

-----------------------

PutSeqPos(s, pos, x) ==
    LET
        nil_list_len == pos - Len(s) - 1
        nil_list == [i \in 1..nil_list_len |-> nil]
    IN
    IF Len(s) >= pos
        THEN [s EXCEPT ![pos] = x]
        ELSE s \o nil_list \o <<x>>

GetSeqPos(s, pos) ==
    IF Len(s) >= pos
        THEN s[pos]
        ELSE nil

ASSUME PutSeqPos(<<12>>, 3, 10) = <<12, nil, 10>>
ASSUME PutSeqPos(<<11, 12, 13>>, 2, 22) = <<11, 22, 13>>
ASSUME GetSeqPos(<<11, 12, 13>>, 2) = 12
ASSUME GetSeqPos(<<11, 12, 13>>, 3) = 13
ASSUME GetSeqPos(<<11, 12, 13>>, 4) = nil

-----------------------

MinOf(S) == CHOOSE x \in S: (\A y \in S: y >= x)

ASSUME MinOf({12, 13, 14}) = 12

MaxOf(S) == CHOOSE x \in S: (\A y \in S: y <= x)

ASSUME MaxOf({12, 13, 14}) = 14

-----------------------

\* return Len(s) + 1 if no elem matched
FindFirstIndex(s, pred(_)) ==
    LET
        values == {i \in DOMAIN s: pred(s[i])}
    IN
    MinOf(values \union {Len(s) + 1})

ASSUME FindFirstIndex(<<12, 13, 14>>, LAMBDA x: x > 13) = 3
ASSUME FindFirstIndex(<<12, 13, 14>>, LAMBDA x: x > 18) = 4

-----------------------

RemoveSeqBefore(s, pos) ==
    SubSeq(s, pos, Len(s))

ASSUME RemoveSeqBefore(<<11, 12, 13>>, 3) = <<13>>
ASSUME RemoveSeqBefore(<<11, 12, 13>>, 5) = <<>>
ASSUME RemoveSeqBefore(<<>>, 2) = <<>>

-----------------------

MapSeq(s, fn(_)) ==
    [i \in DOMAIN s |-> fn(s[i])]

ASSUME MapSeq(<<11, 12, 13>>, LAMBDA x: x + 10) = <<21, 22, 23>>

-----------------------

SubSeqSafe(s, i, j) ==
    IF i > Len(s)
        THEN <<>>
        ELSE SubSeq(s, i, j)

-----------------------

\* Allow b to be infinity
log_pos_less(a, b) ==
    IF b = infinity
        THEN TRUE
        ELSE a < b

-----------------------

FiniteSeq(S, n) ==
    LET
        seq_of(k) == [1..k -> S]
    IN
        UNION {seq_of(k): k \in 0..n}

====

------ MODULE Utils ----

EXTENDS Naturals, Sequences, FiniteSets

AppendFrom(seq, pos, list) ==
    LET
        tmp_len == pos - 1 + Len(list)
        new_len ==
            IF tmp_len < Len(seq)
                THEN Len(seq)
                ELSE tmp_len

        sub_index(i) == i - pos + 1

        choose_fn(i) ==
            IF i < pos THEN
                seq[i]
            ELSE IF sub_index(i) <= Len(list) THEN
                list[sub_index(i)]
            ELSE
                seq[i]
    IN
        [i \in 1..new_len |-> choose_fn(i)]

ASSUME AppendFrom(<<11, 12, 13>>, 4, <<14, 15>>) = <<11, 12, 13, 14, 15>>
ASSUME AppendFrom(<<11, 12, 13>>, 2, <<14, 15>>) = <<11, 14, 15>>
ASSUME AppendFrom(<<11, 12, 13, 14>>, 2, <<21, 22>>) = <<11, 21, 22, 14>>

----------------

IsQuorumOf(U, input_set) ==
    LET
        factor == Cardinality(U) \div 2 + 1
        set == input_set \intersect U
    IN
        Cardinality(set) >= factor

ASSUME IsQuorumOf({11, 12, 13}, {11, 12}) = TRUE
ASSUME IsQuorumOf({11, 12, 13}, {11, 12, 13}) = TRUE
ASSUME IsQuorumOf({11, 12}, {11, 12}) = TRUE
ASSUME IsQuorumOf({11, 12}, {11}) = FALSE
ASSUME IsQuorumOf({11, 12, 13}, {12}) = FALSE
ASSUME IsQuorumOf({11, 12, 13}, {12, 14}) = FALSE


SeqN(S, n) ==
    UNION {[1..k -> S]: k \in 0..n}

ASSUME <<>> \in SeqN({11, 12, 13}, 2)
ASSUME <<12>> \in SeqN({11, 12, 13}, 2)
ASSUME <<12, 13>> \in SeqN({11, 12, 13}, 2)

----------------

MinOf(S) == CHOOSE x \in S: (\A y \in S: y >= x)
MaxOf(S) == CHOOSE x \in S: (\A y \in S: y <= x)

ASSUME MinOf({11, 12, 13}) = 11
ASSUME MaxOf({11, 12, 13}) = 13

----------------

PutToSequenceWithDefault(seq, pos, x, default) ==
    LET
        old_len == Len(seq)
        new_len ==
            IF pos > old_len
                THEN pos
                ELSE old_len

        update_fn(i) ==
            IF i = pos THEN
                x
            ELSE IF i > old_len THEN
                default
            ELSE
                seq[i]
    IN
        [i \in 1..new_len |-> update_fn(i)]


ASSUME PutToSequenceWithDefault(<<11, 12>>, 4, 14, "nil") = <<11, 12, "nil", 14>>
ASSUME PutToSequenceWithDefault(<<11, 12, 13>>, 2, 14, "nil") = <<11, 14, 13>>

====

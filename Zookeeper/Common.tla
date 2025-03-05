------ MODULE Common ----

EXTENDS Naturals

Range(f) == {f[x]: x \in DOMAIN f}

IsMapOf(m, D, R) ==
    /\ DOMAIN m \subseteq D
    /\ Range(m) \subseteq R

mapPut(m, k, v) ==
    LET
        new_domain == (DOMAIN m) \union {k}

        updated(x) ==
            IF x = k
                THEN v
                ELSE m[x]
    IN
    [x \in new_domain |-> updated(x)]

ASSUME mapPut(<<3, 4>>, 1, 4) = <<4, 4>>
ASSUME mapPut(<<3, 4>>, 3, 5) = <<3, 4, 5>>

mapDelete(m, k) ==
    LET
        new_domain == (DOMAIN m) \ {k}
    IN
    [x \in new_domain |-> m[x]]

ASSUME mapDelete(<<3, 4, 5>>, 3) = <<3, 4>>

----------------------------------------------------------

minOf(S) == CHOOSE x \in S: (\A y \in S: y >= x)

maxOf(S) == CHOOSE x \in S: (\A y \in S: y <= x)

ASSUME minOf({4, 2, 3}) = 2
ASSUME maxOf({4, 2, 3}) = 4

----------------------------------------------------------

seqRange(a, b) ==
    LET num == b - a + 1 IN
    [i \in 1..num |-> a + i - 1]

ASSUME seqRange(4, 6) = <<4, 5, 6>>

----------------------------------------------------------

seqMap(s, fn(_)) ==
    [i \in DOMAIN s |-> fn(s[i])]

test_map_fn(x) == x * 2

ASSUME seqMap(<<2, 3, 4>>, test_map_fn) = <<4, 6, 8>>

====

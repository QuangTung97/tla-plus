------ MODULE Paxos ----
EXTENDS TLC, Integers, FiniteSets

CONSTANTS Acceptor, Value, majority, max_ballot_num, nil

Quorum == {Q \in SUBSET Acceptor: Cardinality(Q) = majority}

ASSUME \A Q1, Q2 \in Quorum: Q1 \intersect Q2 # {}

----------------------------------------------------------------

VARIABLES ballot, value, request, response

vars == <<ballot, value, request, response>>

Ballot == 21..max_ballot_num

NullBallot == Ballot \union {nil}

NullValue == Value \union {nil}

Request ==
    LET
        phase1a == [type: {"Phase1a"}, bal: Ballot, val: Value]
    IN
        phase1a

Response ==
    LET
        phase1b == [
            type: {"Phase1b"},
            bal: Ballot,
            acc: Acceptor,
            val: Value
        ]
    IN
        phase1b

----------------------------------------------------------------

TypeOK ==
    /\ ballot \in [Acceptor -> NullBallot]
    /\ value \in [Acceptor -> NullValue]
    /\ request \subseteq Request
    /\ response \subseteq Response

Init ==
    /\ ballot = [a \in Acceptor |-> nil]
    /\ value = [a \in Acceptor |-> nil]
    /\ request = {}
    /\ response = {}

----------------------------------------------------------------

maxOf(S) ==
    CHOOSE x \in S: (\A x1 \in S: x1 <= x)

phase1a_req_set == {req \in request: req.type = "Phase1a"}

Phase1a(v) ==
    LET
        current_bal_set == {req.bal: req \in phase1a_req_set}

        max_bal ==
            IF phase1a_req_set = {}
                THEN 20
                ELSE maxOf(current_bal_set)

        new_req == [
            type |-> "Phase1a",
            bal |-> max_bal + 1,
            val |-> v
        ]
    IN
    /\ max_bal < max_ballot_num
    /\ request' = request \union {new_req}
    /\ UNCHANGED response
    /\ UNCHANGED <<ballot, value>>


nullLessThan(a, b) ==
    IF a = nil
        THEN TRUE
        ELSE a < b

Phase1b(a) ==
    \E req \in request:
        LET
            resp == [
                type |-> "Phase1b",
                acc |-> a,
                bal |-> req.bal,
                val |-> req.val
            ]
        IN
        /\ req.type = "Phase1a"
        /\ nullLessThan(ballot[a], req.bal)

        /\ ballot' = [ballot EXCEPT ![a] = req.bal]
        /\ value' = [value EXCEPT ![a] = req.val]
        /\ response' = response \union {resp}

        /\ UNCHANGED request

----------------------------------------------------------------

TerminateCond ==
    /\ TRUE

Terminated ==
    /\ TerminateCond
    /\ UNCHANGED vars


Next ==
    \/ \E v \in Value: Phase1a(v)
    \/ \E a \in Acceptor:
        \/ Phase1b(a)
    \/ Terminated

Spec == Init /\ [][Next]_vars

----------------------------------------------------------------

IsChosenInBallot(v, b) ==
    \E Q \in Quorum:
        \A a \in Q:
            LET
                resp == [
                    type |-> "Phase1b",
                    acc |-> a,
                    bal |-> b,
                    val |-> v
                ]
            IN
                resp \in response

IsChosen(v) ==
    \E b \in Ballot: IsChosenInBallot(v, b)

ChosenSet == {v \in Value: IsChosen(v)}

Consensus == Cardinality(ChosenSet) <= 1

====

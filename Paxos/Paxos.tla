------ MODULE Paxos ----
EXTENDS TLC, Integers, FiniteSets

CONSTANTS Acceptor, Value, majority, max_ballot_num, nil

Quorum == {Q \in SUBSET Acceptor: Cardinality(Q) = majority}

ASSUME \A Q1, Q2 \in Quorum: Q1 \intersect Q2 # {}

----------------------------------------------------------------

VARIABLES ballot, value, value_ballot,
    request, response, accepted

vars == <<ballot, value, value_ballot,
    request, response, accepted>>

Ballot == 21..max_ballot_num

NullBallot == Ballot \union {nil}

NullValue == Value \union {nil}

Request ==
    LET
        propose_phase == [type: {"Propose"}, bal: Ballot]

        accept_phase == [type: {"Accept"}, bal: Ballot, val: Value]
    IN
        propose_phase \union accept_phase

Response ==
    LET
        propose_resp == [
            type: {"Propose"},
            bal: Ballot,
            acc: Acceptor,
            val: NullValue,
            val_bal: NullBallot
        ]
    IN
        propose_resp

----------------------------------------------------------------

TypeOK ==
    /\ ballot \in [Acceptor -> NullBallot]
    /\ value \in [Acceptor -> NullValue]
    /\ value_ballot \in [Acceptor -> NullBallot]
    /\ request \subseteq Request
    /\ response \subseteq Response
    /\ accepted \subseteq [bal: Ballot, acc: Acceptor, val: Value]

Init ==
    /\ ballot = [a \in Acceptor |-> nil]
    /\ value = [a \in Acceptor |-> nil]
    /\ value_ballot = [a \in Acceptor |-> nil]
    /\ request = {}
    /\ response = {}
    /\ accepted = {}

----------------------------------------------------------------

maxOf(S) ==
    CHOOSE x \in S: (\A x1 \in S: x1 <= x)


request_unchanged ==
    /\ UNCHANGED <<ballot, value, value_ballot>>
    /\ UNCHANGED response
    /\ UNCHANGED accepted


propose_req_set == {req \in request: req.type = "Propose"}

Propose ==
    LET
        current_bal_set == {req.bal: req \in propose_req_set}

        max_bal ==
            IF propose_req_set = {}
                THEN 20
                ELSE maxOf(current_bal_set)

        new_req == [
            type |-> "Propose",
            bal |-> max_bal + 1
        ]
    IN
    /\ max_bal < max_ballot_num
    /\ request' = request \union {new_req}
    /\ request_unchanged


nullLT(a, b) ==
    IF a = nil
        THEN TRUE
        ELSE a < b

nullLE(a, b) ==
    IF a = nil
        THEN TRUE
        ELSE a <= b

HandlePropose(a) ==
    \E req \in request:
        LET
            resp == [
                type |-> "Propose",
                acc |-> a,
                bal |-> req.bal,
                val |-> value[a],
                val_bal |-> value_ballot[a]
            ]
        IN
        /\ req.type = "Propose"
        /\ nullLT(ballot[a], req.bal)

        /\ ballot' = [ballot EXCEPT ![a] = req.bal]
        /\ response' = response \union {resp}

        /\ UNCHANGED <<value, value_ballot>>
        /\ UNCHANGED request
        /\ UNCHANGED accepted


Accept(b, Q, v) ==
    LET
        is_valid_resp(resp, acc) ==
            /\ resp.type = "Propose"
            /\ resp.bal = b
            /\ resp.acc = acc

        resp_set(acc) == {resp \in response: is_valid_resp(resp, acc)}

        resp_with_non_null_val(acc) == {resp \in resp_set(acc): resp.val_bal # nil}

        non_null_val_set == UNION {resp_with_non_null_val(a): a \in Q}

        max_bal == maxOf({resp.val_bal: resp \in non_null_val_set})

        max_value == (CHOOSE resp \in non_null_val_set: resp.val_bal = max_bal).val

        pre_cond ==
            \A a \in Q: resp_set(a) # {}

        exist_accept_req ==
            \E req \in request:
                /\ req.type = "Accept"
                /\ req.bal = b

        new_val_or_max ==
            IF non_null_val_set = {}
                THEN v
                ELSE max_value

        req == [
            type |-> "Accept",
            bal |-> b,
            val |-> new_val_or_max
        ]
    IN
    /\ pre_cond
    /\ ~exist_accept_req
    /\ request' = request \union {req}
    /\ request_unchanged


HandleAccept(a) ==
    \E req \in request:
        LET
            resp == [
                type |-> "Accept",
                bal |-> req.bal
            ]

            new_val == [
                bal |-> req.bal,
                acc |-> a,
                val |-> req.val
            ]
        IN
        /\ req.type = "Accept"
        /\ nullLE(ballot[a], req.bal)
        /\ ballot' = [ballot EXCEPT ![a] = req.bal]
        /\ value' = [value EXCEPT ![a] = req.val]
        /\ value_ballot' = [value_ballot EXCEPT ![a] = req.bal]
        /\ accepted' = accepted \union {new_val}
        /\ UNCHANGED request
        /\ UNCHANGED response

----------------------------------------------------------------

TerminateCond ==
    /\ \A a \in Acceptor: value_ballot[a] = max_ballot_num

Terminated ==
    /\ TerminateCond
    /\ UNCHANGED vars


Next ==
    \/ Propose
    \/ \E a \in Acceptor:
        \/ HandlePropose(a)
        \/ HandleAccept(a)
    \/ \E b \in Ballot, Q \in Quorum, v \in Value: Accept(b, Q, v)
    \/ Terminated

Spec == Init /\ [][Next]_vars

FairSpec == Spec /\ WF_vars(Next)

----------------------------------------------------------------

AlwaysTerminate == <> TerminateCond

IsChosenInBallot(v, b) ==
    \E Q \in Quorum:
        \A a \in Q:
            LET
                accept_val == [
                    bal |-> b,
                    acc |-> a,
                    val |-> v
                ]
            IN
                accept_val \in accepted

IsChosen(v) ==
    \E b \in Ballot: IsChosenInBallot(v, b)

ChosenSet == {v \in Value: IsChosen(v)}

Consensus == Cardinality(ChosenSet) <= 1

====

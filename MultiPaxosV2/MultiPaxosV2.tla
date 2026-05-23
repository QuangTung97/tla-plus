---- MODULE MultiPaxosV2 ----
EXTENDS TLC, Naturals, FiniteSets, Sequences

CONSTANTS Node, nil

VARIABLES
    global_term, state, leader_term, msgs,
    term, log, fully_replicated

leader_vars == <<state, leader_term>>
acceptor_vars == <<term, log, fully_replicated>>

vars == <<
    global_term,
    leader_vars,
    msgs,
    acceptor_vars
>>

------------------------------------------------------------------

QuorumOf(S) ==
    LET
        power_set == SUBSET S
        len == Cardinality(S)
        n == (len \div 2) + 1
    IN
        {x \in power_set: Cardinality(x) = n}

ASSUME QuorumOf({11, 12, 13}) = {{11, 12}, {12, 13}, {13, 11}}
ASSUME QuorumOf({11, 12}) = {{11, 12}}

------------------------------------------------------------------

Term == 20..29

LogPos == 0..9

NullLogPos == LogPos \union {nil}

VoteReqMsg == [
    type: {"VoteReq"},
    term: Term,
    from_pos: LogPos,
    to_node: Node
]

Msg ==
    UNION {VoteReqMsg}

LogEntry == [
    term: Term \* TODO infinity term
]

------------------------------------------------------------------

TypeOK ==
    /\ global_term \in Term
    /\ state \in [Node -> {"Follower", "Candidate", "Leader"}]
    /\ leader_term \in [Node -> Term]
    /\ msgs \subseteq Msg

    /\ term \in Term
    /\ log \in Seq(LogEntry)
    /\ fully_replicated \in [Node -> LogPos]

Init ==
    /\ global_term = 20
    /\ state = [n \in Node |-> "Follower"]
    /\ leader_term = [n \in Node |-> 20]
    /\ msgs = {}

    /\ term = 20
    /\ log = <<>>
    /\ fully_replicated = [n \in Node |-> 0]

------------------------------------------------------------------

StartElection(n) ==
    LET
        vote_req_to(y) == [
            type |-> "VoteReq",
            term |-> leader_term'[n],
            from_pos |-> fully_replicated[n] + 1,
            to_node |-> y
        ]
        req_set == {vote_req_to(y): y \in Node}
    IN
    /\ state[n] = "Follower"
    /\ global_term' = global_term + 1
    /\ leader_term' = [leader_term EXCEPT ![n] = global_term']
    /\ state' = [state EXCEPT ![n] = "Candidate"]
    /\ msgs' = msgs \union req_set
    /\ UNCHANGED acceptor_vars

-------------------------------

------------------------------------------------------------------

Terminated ==
    /\ UNCHANGED vars

-------------------------------

Next ==
    \/ \E n \in Node:
        \/ StartElection(n)
    \/ Terminated

Spec == Init /\ [][Next]_vars

------------------------------------------------------------------

LeaderTermInv ==
    \A n \in Node: leader_term[n] <= global_term

\* TODO add state fields inv

====

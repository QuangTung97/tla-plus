---- MODULE MultiPaxosV2 ----
EXTENDS TLC, Naturals, FiniteSets, Sequences

CONSTANTS Node, nil, infinity, LogValue

VARIABLES
    global_term,
    state, leader_term, remain_map,
    msgs,
    term, log, fully_replicated

leader_vars == <<global_term, state, leader_term, remain_map>>
acceptor_vars == <<term, log, fully_replicated>>

vars == <<
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

Null(S) == S \union {nil}

Term == 20..29

LogPos == 0..9

InfLogPos == LogPos \union {infinity}

LeaderRemainMap == [Node -> Null(InfLogPos)]

-----------------------

LogEntry == [
    term: InfLogPos,
    value: LogValue
]

-----------------------

VoteReqMsg == [
    type: {"VoteReq"},
    term: Term,
    from_pos: LogPos,
    to_node: Node
]

VoteRespMsg == [
    type: {"VoteResp"},
    term: Term,
    from_node: Node,
    more: BOOLEAN,
    pos: LogPos,
    entry: Null(LogEntry)
]

Msg ==
    UNION {VoteReqMsg, VoteRespMsg}

------------------------------------------------------------------

TypeOK ==
    /\ global_term \in Term
    /\ state \in [Node -> {"Follower", "Candidate", "Leader"}]
    /\ leader_term \in [Node -> Term]
    /\ remain_map \in [Node -> Null(LeaderRemainMap)]
    /\ msgs \subseteq Msg

    /\ term \in [Node -> Term]
    /\ log \in Seq(LogEntry)
    /\ fully_replicated \in [Node -> LogPos]

Init ==
    /\ global_term = 20

    /\ state = [n \in Node |-> "Follower"]
    /\ leader_term = [n \in Node |-> 20]
    /\ remain_map = [n \in Node |-> nil]

    /\ msgs = {}

    /\ term = [n \in Node |-> 20]
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

        new_remain_map == [y \in Node |-> fully_replicated[n] + 1]
    IN
    /\ state[n] = "Follower"
    /\ global_term' = global_term + 1
    /\ leader_term' = [leader_term EXCEPT ![n] = global_term']
    /\ state' = [state EXCEPT ![n] = "Candidate"]
    /\ msgs' = msgs \union req_set
    /\ remain_map' = [remain_map EXCEPT ![n] = new_remain_map]
    /\ UNCHANGED acceptor_vars

-----------------------

doHandleVoteResp(n, resp) ==
    LET
        y == resp.from_node

        new_remain_map == [remain_map EXCEPT ![n][y] = infinity]
        inf_set == {x \in Node: remain_map[n][x] = infinity}

        switch_to_leader ==
            inf_set \in QuorumOf(Node)

        when_normal ==
            /\ remain_map' = new_remain_map
            /\ UNCHANGED state

        when_become_leader ==
            /\ state' = [state EXCEPT ![n] = "Leader"]
            /\ remain_map' = [remain_map EXCEPT ![n] = nil]
    IN
    /\ state[n] = "Candidate"
    /\ remain_map[n][y] = resp.pos

    /\ IF switch_to_leader
        THEN when_become_leader
        ELSE when_normal

    /\ UNCHANGED leader_term
    /\ UNCHANGED msgs
    /\ UNCHANGED acceptor_vars
    /\ UNCHANGED global_term

HandleVoteResp(n) ==
    \E resp \in msgs:
        /\ resp.type = "VoteResp"
        /\ resp.term = leader_term[n]
        /\ doHandleVoteResp(n, resp)

------------------------------------------------------------------

doHandleVoteReq(n, req) ==
    LET
        resp == [
            type |-> "VoteResp",
            term |-> req.term,
            from_node |-> n,
            more |-> FALSE,
            pos |-> 1, \* TODO
            entry |-> nil
        ]
    IN
    /\ req.term > term[n]
    /\ term' = [term EXCEPT ![n] = req.term]
    /\ msgs' = msgs \union {resp}
    /\ UNCHANGED <<log, fully_replicated>>
    /\ UNCHANGED leader_vars

HandleVoteReq(n) ==
    \E req \in msgs:
        /\ req.type = "VoteReq"
        /\ req.to_node = n
        /\ doHandleVoteReq(n, req)

------------------------------------------------------------------

Terminated ==
    /\ UNCHANGED vars

-----------------------

Next ==
    \/ \E n \in Node:
        \/ StartElection(n)
        \/ HandleVoteReq(n)
        \/ HandleVoteResp(n)
    \/ Terminated

Spec == Init /\ [][Next]_vars

------------------------------------------------------------------

LeaderTermInv ==
    \A n \in Node: leader_term[n] <= global_term

\* TODO add state fields inv

====

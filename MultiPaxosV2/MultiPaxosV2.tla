---- MODULE MultiPaxosV2 ----
EXTENDS TLC, Naturals, FiniteSets, Sequences

CONSTANTS
    Node, nil, infinity,
    Value, nop, max_log_len

VARIABLES
    global_term,
    state, leader_term, remain_map, mem_log, \* TODO add prepare_log
    msgs,
    acc_term, acc_log, fully_replicated

leader_vars == <<global_term, state, leader_term, remain_map, mem_log>>
acceptor_vars == <<acc_term, acc_log, fully_replicated>>

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

------------------------------------------------------------------

Null(S) == S \union {nil}

Term == 20..29
InfTerm == Term \union {infinity}

LogPos == 0..9

InfLogPos == LogPos \union {infinity}

LeaderRemainMap == [Node -> Null(InfLogPos)]

-----------------------

LogValue == Value \union {nop}

LogEntry == [
    term: InfTerm,
    value: LogValue
]

-----------------------

VoteReqMsg == [
    type: {"VoteReq"},
    term: Term,
    from_pos: LogPos,
    to_node: Node
]

VoteLogEntry == [
    term: InfLogPos,
    value: LogValue
]

VoteRespMsg == [
    type: {"VoteResp"},
    term: Term,
    from_node: Node,
    more: BOOLEAN,
    pos: LogPos,
    entry: Null(VoteLogEntry)
]

AcceptReqMsg == [
    type: {"AcceptReq"},
    term: Term,
    to_node: Node,
    pos: LogPos,
    value: LogValue
]

AcceptRespMsg == [
    type: {"AcceptResp"},
    term: Term,
    from_node: Node,
    pos: LogPos
]

Msg ==
    UNION {VoteReqMsg, VoteRespMsg, AcceptReqMsg, AcceptRespMsg}

-----------------------

MemLogEntry == [
    value: LogValue,
    acceptors: SUBSET Node
]

------------------------------------------------------------------

TypeOK ==
    /\ global_term \in Term

    /\ state \in [Node -> {"Follower", "Candidate", "Leader"}]
    /\ leader_term \in [Node -> Term]
    /\ remain_map \in [Node -> Null(LeaderRemainMap)]
    /\ mem_log \in [Node -> Seq(MemLogEntry)]

    /\ msgs \subseteq Msg

    /\ acc_term \in [Node -> Term]
    /\ acc_log \in [Node -> Seq(Null(LogEntry))]
    /\ fully_replicated \in [Node -> LogPos]

Init ==
    /\ global_term = 20

    /\ state = [n \in Node |-> "Follower"]
    /\ leader_term = [n \in Node |-> 20]
    /\ remain_map = [n \in Node |-> nil]
    /\ mem_log = [n \in Node |-> <<>>]

    /\ msgs = {}

    /\ acc_term = [n \in Node |-> 20]
    /\ acc_log = [n \in Node |-> <<>>]
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
    /\ UNCHANGED mem_log
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
            /\ UNCHANGED mem_log

        when_become_leader ==
            /\ state' = [state EXCEPT ![n] = "Leader"]
            /\ remain_map' = [remain_map EXCEPT ![n] = nil]
            /\ UNCHANGED mem_log
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
    /\ req.term > acc_term[n]
    /\ acc_term' = [acc_term EXCEPT ![n] = req.term]
    /\ msgs' = msgs \union {resp}
    /\ UNCHANGED <<acc_log, fully_replicated>>
    /\ UNCHANGED leader_vars

HandleVoteReq(n) ==
    \E req \in msgs:
        /\ req.type = "VoteReq"
        /\ req.to_node = n
        /\ doHandleVoteReq(n, req)

------------------------------------------------------------------

doNewLeaderCmd(n, v) ==
    LET
        entry == [
            value |-> v,
            acceptors |-> {}
        ]

        pos == Len(mem_log[n]) + 1 \* TODO with fully replicated

        acc_req(y) == [
            type |-> "AcceptReq",
            term |-> leader_term[n],
            to_node |-> y,
            pos |-> pos,
            value |-> v
        ]
        acc_req_set == {acc_req(y): y \in Node}
    IN
    /\ state[n] = "Leader"
    /\ pos <= max_log_len
    /\ mem_log' = [mem_log EXCEPT ![n] = Append(@, entry)]
    /\ msgs' = msgs \union acc_req_set
    /\ UNCHANGED <<state, leader_term, global_term, remain_map>>
    /\ UNCHANGED acceptor_vars

NewLeaderCmd(n) ==
    \E v \in Value: doNewLeaderCmd(n, v)

------------------------------------------------------------------

doHandleAcceptReq(n, req) ==
    LET
        pos == req.pos
        log == acc_log[n]

        prev_entry == GetSeqPos(log, pos)
        new_entry == [
            term |-> req.term,
            value |-> req.value
        ]

        not_allow_update ==
            /\ prev_entry # nil
            /\ \/ prev_entry.term = infinity
               \/ prev_entry.term = req.term

        acc_resp == [
            type |-> "AcceptResp",
            term |-> req.term,
            pos |-> pos,
            from_node |-> n
        ]
    IN
    /\ req.term >= acc_term[n]
    /\ ~not_allow_update
    /\ acc_term' = [acc_term EXCEPT ![n] = req.term]
    /\ acc_log' = [acc_log EXCEPT ![n] = PutSeqPos(@, pos, new_entry)]
    /\ msgs' = msgs \union {acc_resp}
    /\ UNCHANGED fully_replicated
    /\ UNCHANGED leader_vars

HandleAcceptReq(n) ==
    \E req \in msgs:
        /\ req.type = "AcceptReq"
        /\ req.to_node = n
        /\ doHandleAcceptReq(n, req)

------------------------------------------------------------------

Terminated ==
    /\ UNCHANGED vars

-----------------------

Next ==
    \/ \E n \in Node:
        \/ StartElection(n)
        \/ HandleVoteReq(n)
        \/ HandleVoteResp(n)
        \/ NewLeaderCmd(n)
        \/ HandleAcceptReq(n)
    \/ Terminated

Spec == Init /\ [][Next]_vars

------------------------------------------------------------------

LeaderTermInv ==
    \A n \in Node: leader_term[n] <= global_term

\* TODO add state fields inv

====

---- MODULE MultiPaxosV2 ----
EXTENDS TLC, Naturals, FiniteSets, Sequences

CONSTANTS
    Node, nil, infinity,
    Value, nop, max_log_len

VARIABLES
    global_term,
    state, leader_term, mem_fully_repl,
    remain_map, mem_log, commit_log, \* TODO add prepare_log
    msgs,
    acc_term, acc_log,
    god_log

leader_vars == <<
    global_term,
    state, leader_term, mem_fully_repl,
    remain_map, mem_log, commit_log,
    god_log
>>
acceptor_vars == <<acc_term, acc_log>>

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

-----------------------

MinOf(S) == CHOOSE x \in S: (\A y \in S: y >= x)

ASSUME MinOf({12, 13, 14}) = 12

-----------------------

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

-----------------------

MapSeq(s, fn(_)) ==
    [i \in DOMAIN s |-> fn(s[i])]

ASSUME MapSeq(<<11, 12, 13>>, LAMBDA x: x + 10) = <<21, 22, 23>>

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
    acceptors: SUBSET Node,
    committed: BOOLEAN
]

------------------------------------------------------------------

TypeOK ==
    /\ global_term \in Term

    /\ state \in [Node -> {"Follower", "Candidate", "Leader"}]
    /\ leader_term \in [Node -> Term]
    /\ mem_fully_repl \in [Node -> Null(LogPos)]
    /\ remain_map \in [Node -> Null(LeaderRemainMap)]
    /\ mem_log \in [Node -> Seq(MemLogEntry)]
    /\ commit_log \in [Node -> Seq(LogValue)]
    /\ god_log \in Seq(LogValue)

    /\ msgs \subseteq Msg

    /\ acc_term \in [Node -> Term]
    /\ acc_log \in [Node -> Seq(Null(LogEntry))]

Init ==
    /\ global_term = 20

    /\ state = [n \in Node |-> "Follower"]
    /\ leader_term = [n \in Node |-> 20]
    /\ mem_fully_repl = [n \in Node |-> nil]
    /\ remain_map = [n \in Node |-> nil]
    /\ mem_log = [n \in Node |-> <<>>]
    /\ commit_log = [n \in Node |-> <<>>]
    /\ god_log = <<>>

    /\ msgs = {}

    /\ acc_term = [n \in Node |-> 20]
    /\ acc_log = [n \in Node |-> <<>>]

------------------------------------------------------------------

StartElection(n) ==
    LET
        fully_replicated == 0 \* TODO

        start_pos == fully_replicated + 1

        vote_req_to(y) == [
            type |-> "VoteReq",
            term |-> leader_term'[n],
            from_pos |-> start_pos,
            to_node |-> y
        ]
        req_set == {vote_req_to(y): y \in Node}

        new_remain_map == [y \in Node |-> start_pos]
    IN
    /\ state[n] = "Follower"
    /\ global_term' = global_term + 1
    /\ leader_term' = [leader_term EXCEPT ![n] = global_term']
    /\ mem_fully_repl' = [mem_fully_repl EXCEPT ![n] = fully_replicated]
    /\ state' = [state EXCEPT ![n] = "Candidate"]
    /\ msgs' = msgs \union req_set
    /\ remain_map' = [remain_map EXCEPT ![n] = new_remain_map]
    /\ UNCHANGED <<mem_log, commit_log, god_log>>
    /\ UNCHANGED acceptor_vars

-----------------------

doHandleVoteResp(n, resp) ==
    LET
        y == resp.from_node

        new_remain_map == [remain_map EXCEPT ![n][y] = infinity]
        inf_set == {x \in Node: new_remain_map[n][x] = infinity}

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

    /\ UNCHANGED <<leader_term, mem_fully_repl, commit_log, god_log>>
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
    /\ UNCHANGED acc_log
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
            acceptors |-> {},
            committed |-> FALSE
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
    /\ UNCHANGED <<mem_fully_repl, commit_log, god_log>>
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
    /\ UNCHANGED leader_vars

HandleAcceptReq(n) ==
    \E req \in msgs:
        /\ req.type = "AcceptReq"
        /\ req.to_node = n
        /\ doHandleAcceptReq(n, req)

------------------------------------------------------------------

doHandleAcceptResp(n, resp) ==
    LET
        pos == resp.pos
        y == resp.from_node
        mem_log_start == mem_fully_repl[n] + 1 + Len(commit_log[n])
        index == pos - mem_log_start + 1

        new_mem_log == [mem_log EXCEPT ![n][index].acceptors = @ \union {y}]

        is_committed ==
            new_mem_log[n][index].acceptors \in QuorumOf(Node)

        set_committed == [new_mem_log EXCEPT ![n][index].committed = is_committed]
        new_log == set_committed[n]

        first_non_commit == FindFirstIndex(new_log, LAMBDA entry: ~entry.committed)

        new_committed == SubSeq(new_log, 1, first_non_commit - 1)
        new_committed_values == MapSeq(new_committed, LAMBDA entry: entry.value)
    IN
    /\ pos >= mem_log_start
    /\ y \notin mem_log[n][index].acceptors
    /\ mem_log' = [set_committed EXCEPT ![n] = RemoveSeqBefore(@, first_non_commit)]
    /\ commit_log' = [commit_log EXCEPT ![n] = @ \o new_committed_values]
    /\ IF Len(commit_log'[n]) > Len(god_log)
        THEN god_log' = commit_log'[n]
        ELSE UNCHANGED god_log
    /\ UNCHANGED msgs
    /\ UNCHANGED mem_fully_repl
    /\ UNCHANGED <<leader_term, global_term, state, remain_map>>
    /\ UNCHANGED acceptor_vars

HandleAcceptResp(n) ==
    \E resp \in msgs:
        /\ resp.type = "AcceptResp"
        /\ resp.term = leader_term[n]
        /\ doHandleAcceptResp(n, resp)

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
        \/ HandleAcceptResp(n)
    \/ Terminated

Spec == Init /\ [][Next]_vars

------------------------------------------------------------------

LeaderTermInv ==
    \A n \in Node: leader_term[n] <= global_term


godLogStep ==
    LET
        new_len == Len(god_log')
        old_len == Len(god_log)
    IN
    /\ new_len > old_len
    /\ SubSeq(god_log', 1, old_len) = god_log

GodLogProperty ==
    [][godLogStep]_god_log


GodLogMatchCommitLog ==
    \A n \in Node:
        commit_log[n] = SubSeq(god_log, 1, Len(commit_log[n]))


\* TODO add state fields inv
\* TODO acc_log and fully_replicated inv


InversedInv ==
    Len(god_log) = 0

====

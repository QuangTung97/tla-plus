------ MODULE MultiPaxos ----
EXTENDS TLC, Naturals, FiniteSets, Sequences

CONSTANTS Node, nil, infinity, max_start_election

---------------------------------------------------------------

VARIABLES
    num_start_election,
    members, log, state, last_committed,
    global_last_term, last_propose_term, last_term,
    candidate_remain_pos, mem_log,
    msgs, last_cmd_num

leader_vars == <<
    num_start_election,
    global_last_term,
    members, state, last_committed,
    last_propose_term,
    candidate_remain_pos, mem_log
>>

acceptor_vars == <<log, last_term>>

vars == <<
    acceptor_vars,
    leader_vars,
    msgs,
    last_cmd_num
>>

---------------------------------------------------------------

TermNum == 20..25
NullTerm == TermNum \union {nil}

LogPos == (0..20)
NullLogPos == LogPos \union {nil, infinity}

max_cmd_num == 32
CmdNum == 30..max_cmd_num

LogEntry ==
    LET
        membership== [
            type: {"Member"},
            committed: BOOLEAN,
            term: NullTerm,
            nodes: SUBSET Node
        ]

        null_entry == [
            type: {"Null"},
            committed: BOOLEAN,
            term: NullTerm
        ]

        cmd_entry == [
            type: {"Cmd"},
            committed: BOOLEAN,
            term: NullTerm,
            cmd: CmdNum
        ]
    IN
        UNION {membership, null_entry, cmd_entry}

NullLogEntry == LogEntry \union {nil}

Message ==
    LET
        request_vote == [
            type: {"RequestVote"},
            from: Node,
            term: TermNum,
            log_pos: LogPos,
            recv: SUBSET Node
        ]

        vote_response == [
            type: {"VoteResponse"},
            from: Node,
            to: Node,
            term: TermNum,
            log_pos: LogPos,
            entry: NullLogEntry,
            more: BOOLEAN
        ]

        accept_entry == [
            type: {"AcceptEntry"},
            term: TermNum,
            from: Node,
            log_pos: LogPos,
            entry: LogEntry,
            recv: SUBSET Node
        ]

        accept_resp == [
            type: {"AcceptResponse"},
            term: TermNum,
            log_pos: LogPos,
            from: Node,
            to: Node
        ]
    IN
        UNION {request_vote, vote_response, accept_entry, accept_resp}


IsQuorum(n, set) ==
    LET
        factor == Cardinality(members[n]) \div 2 + 1
    IN
        Cardinality(set) >= factor

---------------------------------------------------------------

RemainPosition ==
    [Node -> NullLogPos] \union {nil}

TypeOK ==
    /\ num_start_election \in 0..max_start_election
    /\ members \in [Node -> SUBSET Node]
    /\ log \in [Node -> Seq(NullLogEntry)]
    /\ last_committed \in [Node -> LogPos]
    /\ state \in [Node -> {"Follower", "Candidate", "Leader"}]
    /\ global_last_term \in TermNum
    /\ last_propose_term \in [Node -> TermNum]
    /\ last_term \in [Node -> TermNum]
    /\ candidate_remain_pos \in [Node -> RemainPosition]
    /\ mem_log \in [Node -> Seq(LogEntry)]
    /\ msgs \subseteq Message
    /\ last_cmd_num \in CmdNum

init_members ==
    \E S \in SUBSET Node:
        LET
            init_nodes(n) ==
                IF n \in S
                    THEN S
                    ELSE {}

            init_entry == [
                type |-> "Member",
                committed |-> TRUE,
                term |-> nil,
                nodes |-> S
            ]

            init_logs(n) ==
                IF n \in S
                    THEN <<init_entry>>
                    ELSE <<>>

            init_last_committed(n) ==
                IF n \in S
                    THEN 1
                    ELSE 0
        IN
        /\ S # {}
        /\ members = [n \in Node |-> init_nodes(n)]
        /\ log = [n \in Node |-> init_logs(n)]
        /\ last_committed = [n \in Node |-> init_last_committed(n)]

Init ==
    /\ num_start_election = 0
    /\ init_members
    /\ state = [n \in Node |-> "Follower"]
    /\ global_last_term = 20
    /\ last_propose_term = [n \in Node |-> 20]
    /\ last_term = [n \in Node |-> 20]
    /\ candidate_remain_pos = [n \in Node |-> nil]
    /\ mem_log = [n \in Node |-> <<>>]
    /\ msgs = {}
    /\ last_cmd_num = 30

---------------------------------------------------------------

StartElection(n) ==
    LET
        req == [
            type |-> "RequestVote",
            from |-> n,
            term |-> last_propose_term'[n],
            log_pos |-> last_committed[n] + 1,
            recv |-> members[n]
        ]

        init_remain_pos == [n1 \in Node |->
            IF n1 \in members[n]
                THEN last_committed[n] + 1
                ELSE nil
        ]
    IN
    /\ n \in members[n]
    /\ state[n] = "Follower"
    /\ num_start_election < max_start_election
    /\ num_start_election' = num_start_election + 1

    /\ global_last_term' = global_last_term + 1
    /\ state' = [state EXCEPT ![n] = "Candidate"]
    /\ last_propose_term' = [last_propose_term EXCEPT ![n] = global_last_term']
    /\ candidate_remain_pos' = [candidate_remain_pos EXCEPT ![n] = init_remain_pos]

    /\ msgs' = msgs \union {req}

    /\ UNCHANGED mem_log
    /\ UNCHANGED last_committed
    /\ UNCHANGED members
    /\ UNCHANGED acceptor_vars
    /\ UNCHANGED last_cmd_num


HandleRequestVote(n) ==
    \E req \in msgs:
        LET
            resp == [
                type |-> "VoteResponse",
                from |-> n,
                to |-> req.from,
                term |-> req.term,
                log_pos |-> req.log_pos,
                entry |-> nil,
                more |-> FALSE
            ]
        IN
        /\ req.type = "RequestVote"
        /\ n \in req.recv
        /\ last_term[n] < req.term
        /\ last_term' = [last_term EXCEPT ![n] = req.term]
        /\ msgs' = msgs \union {resp}

        /\ UNCHANGED log
        /\ UNCHANGED leader_vars
        /\ UNCHANGED last_cmd_num


doHandleVoteResponse(n, resp) ==
    LET
        from == resp.from
        remain_pos == candidate_remain_pos[n][from]

        inc_pos ==
            candidate_remain_pos' = [
                candidate_remain_pos EXCEPT ![n][from] = @ + 1]

        set_pos_inf ==
            candidate_remain_pos' = [
                candidate_remain_pos EXCEPT ![n][from] = infinity]

        update_remain ==
            IF resp.more
                THEN inc_pos
                ELSE set_pos_inf

        new_pos_map == candidate_remain_pos'[n]

        is_non_inf(n1) ==
            /\ new_pos_map[n1] # nil
            /\ new_pos_map[n1] # infinity

        entry_checked_set == {n1 \in DOMAIN new_pos_map:
                is_non_inf(n1) => (new_pos_map[n1] >= remain_pos)
            }
        entry_achieve_quorum == IsQuorum(n, entry_checked_set)

        update_mem_log ==
            /\ TRUE \* TODO

        accept_req == [
            type |-> "AcceptEntry",
            term |-> resp.term, \* TODO
            recv |-> members[n]
        ]

        inf_set == {n1 \in DOMAIN new_pos_map: new_pos_map[n1] = infinity}
    IN
    /\ resp.type = "VoteResponse"
    /\ state[n] = "Candidate"
    /\ last_propose_term[n] = resp.term
    /\ remain_pos # nil
    /\ remain_pos = resp.log_pos

    /\ update_remain
    /\ IF resp.entry = nil
        THEN UNCHANGED mem_log
        ELSE update_mem_log

    /\ IF entry_achieve_quorum /\ resp.more
        THEN msgs' = msgs \union {accept_req}
        ELSE UNCHANGED msgs

    /\ IF IsQuorum(n, inf_set)
        THEN state' = [state EXCEPT ![n] = "Leader"]
        ELSE UNCHANGED state

    /\ UNCHANGED num_start_election
    /\ UNCHANGED last_propose_term
    /\ UNCHANGED global_last_term
    /\ UNCHANGED last_committed
    /\ UNCHANGED members
    /\ UNCHANGED acceptor_vars
    /\ UNCHANGED last_cmd_num

HandleVoteResponse(n) ==
    \E resp \in msgs: doHandleVoteResponse(n, resp)

---------------------------------------------------------------

NewCommand(n) ==
    LET
        log_entry == [
            type |-> "Cmd",
            term |-> last_propose_term[n],
            committed |-> FALSE,
            cmd |-> last_cmd_num'
        ]

        log_pos == last_committed[n] + Len(mem_log'[n])

        accept_req == [
            type |-> "AcceptEntry",
            term |-> last_propose_term[n],
            from |-> n,
            log_pos |-> log_pos,
            entry |-> log_entry,
            recv |-> members[n]
        ]
    IN
    /\ state[n] = "Leader"

    /\ last_cmd_num < max_cmd_num
    /\ last_cmd_num' = last_cmd_num + 1

    /\ mem_log' = [mem_log EXCEPT ![n] = Append(@, log_entry)]
    /\ msgs' = msgs \union {accept_req}

    /\ UNCHANGED state
    /\ UNCHANGED num_start_election
    /\ UNCHANGED candidate_remain_pos
    /\ UNCHANGED last_propose_term
    /\ UNCHANGED global_last_term
    /\ UNCHANGED last_committed
    /\ UNCHANGED members
    /\ UNCHANGED acceptor_vars


putToLog(n, entry, pos) ==
    LET
        old_len == Len(log[n])
        new_len ==
            IF pos > old_len
                THEN pos
                ELSE old_len

        update_log(i) ==
            IF i = pos THEN
                entry
            ELSE IF i > old_len THEN
                nil
            ELSE
                log[n][i]

        new_log == [i \in 1..new_len |-> update_log(i)]
    IN
        [log EXCEPT ![n] = new_log]


doAcceptEntry(n, req) ==
    LET
        resp == [
            type |-> "AcceptResponse",
            term |-> req.term,
            from |-> n,
            to |-> req.from,
            log_pos |-> req.log_pos
        ]
    IN
    /\ req.type = "AcceptEntry"
    /\ n \in req.recv
    /\ req.term >= last_term[n]

    /\ last_term' = [last_term EXCEPT ![n] = req.term]
    /\ msgs' = msgs \union {resp}
    /\ log' = putToLog(n, req.entry, req.log_pos)


    /\ UNCHANGED leader_vars
    /\ UNCHANGED last_cmd_num

AcceptEntry(n) ==
    \E req \in msgs: doAcceptEntry(n, req)

---------------------------------------------------------------

TerminateCond ==
    /\ num_start_election = max_start_election
    /\ \A n \in Node: mem_log[n] = <<>>

Terminated ==
    /\ TerminateCond
    /\ UNCHANGED vars


Next ==
    \/ \E n \in Node:
        \/ StartElection(n)
        \/ HandleRequestVote(n)
        \/ HandleVoteResponse(n)
        \/ NewCommand(n)
        \/ AcceptEntry(n)
    \/ Terminated

Spec == Init /\ [][Next]_vars


====

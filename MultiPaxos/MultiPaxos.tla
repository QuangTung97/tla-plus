------ MODULE MultiPaxos ----
EXTENDS TLC, Naturals, FiniteSets, Sequences

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

IsQuorumOf(U, set) ==
    LET
        factor == Cardinality(U) \div 2 + 1
    IN
        Cardinality(set) >= factor

ASSUME IsQuorumOf({11, 12, 13}, {11, 12}) = TRUE
ASSUME IsQuorumOf({11, 12, 13}, {11, 12, 13}) = TRUE
ASSUME IsQuorumOf({11, 12}, {11, 12}) = TRUE
ASSUME IsQuorumOf({11, 12}, {11}) = FALSE
ASSUME IsQuorumOf({11, 12, 13}, {12}) = FALSE

---------------------------------------------------------------

CONSTANTS Node, nil, infinity, max_start_election, total_num_cmd

MinOf(S) == CHOOSE x \in S: (\A y \in S: y >= x)
MaxOf(S) == CHOOSE x \in S: (\A y \in S: y <= x)

putToSequence(seq, pos, x) ==
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
                nil
            ELSE
                seq[i]
    IN
        [i \in 1..new_len |-> update_fn(i)]


lessThanWithInf(x, y) ==
    IF x = infinity THEN
        FALSE
    ELSE
        IF y = infinity
            THEN TRUE
            ELSE x < y

ASSUME lessThanWithInf(infinity, infinity) = FALSE
ASSUME lessThanWithInf(infinity, 70) = FALSE
ASSUME lessThanWithInf(70, 71) = TRUE
ASSUME lessThanWithInf(70, infinity) = TRUE
ASSUME lessThanWithInf(72, 71) = FALSE

---------------------------------------------------------------

VARIABLES
    log, last_term, committed_upper, current_leader,
    global_last_term,
    members, state, last_committed,
    last_propose_term,
    mem_log, log_voted,
    last_cmd_num,
    candidate_remain_pos, candidate_accept_pos,
    msgs, god_log

candidate_vars == <<
    candidate_remain_pos, candidate_accept_pos
>>

leader_vars == <<
    global_last_term,
    members, state, last_committed,
    last_propose_term,
    mem_log, log_voted,
    last_cmd_num
>>

acceptor_vars == <<
    log, last_term, committed_upper, current_leader
>>

vars == <<
    acceptor_vars,
    leader_vars,
    candidate_vars,
    msgs, god_log
>>

---------------------------------------------------------------

NullNode == Node \union {nil}

max_term_num == 20 + max_start_election
TermNum == 20..max_term_num
TermNumInf == TermNum \union {infinity}

LogPos == (0..20)
NullLogPos == LogPos \union {nil}
InfLogPos == NullLogPos \union {infinity}

max_cmd_num == 30 + total_num_cmd
CmdNum == 30..max_cmd_num

LogEntry ==
    LET
        membership== [
            type: {"Member"},
            term: TermNumInf,
            committed: BOOLEAN,
            nodes: SUBSET Node
        ]

        null_entry == [
            type: {"Null"},
            term: TermNumInf,
            committed: BOOLEAN
        ]

        cmd_entry == [
            type: {"Cmd"},
            term: TermNumInf,
            committed: BOOLEAN,
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

        accept_failed == [
            type: {"AcceptFailed"},
            term: TermNum,
            to: Node
        ]
    IN
        UNION {
            request_vote, vote_response,
            accept_entry, accept_resp, accept_failed
        }


IsQuorum(n, set) ==
    LET
        factor == Cardinality(members[n]) \div 2 + 1
    IN
        Cardinality(set) >= factor

---------------------------------------------------------------

RemainPosition ==
    [Node -> InfLogPos] \union {nil}

TypeOK ==
    /\ log \in [Node -> Seq(NullLogEntry)]
    /\ last_term \in [Node -> TermNum]
    /\ committed_upper \in [Node -> LogPos]
    /\ current_leader \in [Node -> NullNode]
    /\ god_log \in Seq(NullLogEntry)

    /\ state \in [Node -> {"Follower", "Candidate", "Leader"}]
    /\ members \in [Node -> SUBSET Node]
    /\ last_committed \in [Node -> NullLogPos]
    /\ global_last_term \in TermNum
    /\ last_propose_term \in [Node -> TermNum]

    /\ mem_log \in [Node -> Seq(LogEntry)]
    /\ log_voted \in [Node -> Seq(SUBSET Node)]
    /\ last_cmd_num \in CmdNum

    /\ candidate_remain_pos \in [Node -> RemainPosition]
    /\ candidate_accept_pos \in [Node -> NullLogPos]

    /\ msgs \subseteq Message

init_members ==
    \E S \in SUBSET Node:
        LET
            init_nodes(n) ==
                IF n \in S
                    THEN S
                    ELSE {}

            init_entry == [
                type |-> "Member",
                term |-> infinity,
                committed |-> TRUE,
                nodes |-> S
            ]

            init_logs(n) ==
                IF n \in S
                    THEN <<init_entry>>
                    ELSE <<>>

            init_committed(n) ==
                IF n \in S
                    THEN 1
                    ELSE 0
        IN
        /\ S # {}
        /\ members = [n \in Node |-> init_nodes(n)]
        /\ log = [n \in Node |-> init_logs(n)]
        /\ committed_upper = [n \in Node |-> init_committed(n)]
        /\ god_log = <<init_entry>>

Init ==
    /\ init_members
    /\ last_term = [n \in Node |-> 20]
    /\ current_leader = [n \in Node |-> nil]

    /\ state = [n \in Node |-> "Follower"]
    /\ last_committed = [n \in Node |-> nil]
    /\ global_last_term = 20
    /\ last_propose_term = [n \in Node |-> 20]

    /\ mem_log = [n \in Node |-> <<>>]
    /\ log_voted = [n \in Node |-> <<>>]
    /\ last_cmd_num = 30

    /\ candidate_remain_pos = [n \in Node |-> nil]
    /\ candidate_accept_pos = [n \in Node |-> nil]

    /\ msgs = {}

----------------------

setLogCommitted(input_log, n, pos) ==
    [input_log EXCEPT
            ![n][pos].committed = TRUE,
            ![n][pos].term = infinity
        ]

setLogCommittedEntry(entry) ==
    [entry EXCEPT !.committed = TRUE, !.term = infinity]

getLogEntryNull(input_log, pos) ==
    LET
        cond ==
            /\ Len(input_log) >= pos
            /\ input_log[pos] # nil
    IN
        IF cond
            THEN input_log[pos]
            ELSE nil

---------------------------------------------------------------

StartElection(n) ==
    LET
        commit_index == committed_upper[n]

        req == [
            type |-> "RequestVote",
            from |-> n,
            term |-> last_propose_term'[n],
            log_pos |-> commit_index + 1,
            recv |-> members[n]
        ]

        init_remain_pos == [n1 \in Node |->
            IF n1 \in members[n]
                THEN commit_index + 1
                ELSE nil
        ]
    IN
    /\ n \in members[n]
    /\ state[n] = "Follower"

    /\ global_last_term < max_term_num
    /\ global_last_term' = global_last_term + 1

    /\ state' = [state EXCEPT ![n] = "Candidate"]
    /\ last_propose_term' = [last_propose_term EXCEPT ![n] = global_last_term']
    /\ candidate_remain_pos' = [candidate_remain_pos EXCEPT ![n] = init_remain_pos]
    /\ candidate_accept_pos' = [candidate_accept_pos EXCEPT ![n] = commit_index]

    /\ msgs' = msgs \union {req}
    /\ last_committed' = [last_committed EXCEPT ![n] = commit_index]

    /\ UNCHANGED <<mem_log, log_voted>>
    /\ UNCHANGED members
    /\ UNCHANGED acceptor_vars
    /\ UNCHANGED last_cmd_num
    /\ UNCHANGED god_log

---------------------------------------------------------------

RECURSIVE buildVoteResponses(_, _, _, _)

buildVoteResponses(input_log, n, req, pos) ==
    LET
        resp == [
            type |-> "VoteResponse",
            from |-> n,
            to |-> req.from,
            term |-> req.term,
            log_pos |-> pos,
            entry |-> input_log[1],
            more |-> TRUE
        ]

        final_resp == [
            type |-> "VoteResponse",
            from |-> n,
            to |-> req.from,
            term |-> req.term,
            log_pos |-> pos,
            entry |-> nil,
            more |-> FALSE
        ]
    IN
    IF Len(input_log) = 0
        THEN {final_resp}
        ELSE {resp} \union buildVoteResponses(
            Tail(input_log), n, req, pos + 1
        )


HandleRequestVote(n) ==
    \E req \in msgs:
        LET
            log_len == Len(log[n])
            vote_logs ==
                IF req.log_pos > log_len
                    THEN <<>>
                    ELSE SubSeq(log[n], req.log_pos, log_len)
        IN
        /\ req.type = "RequestVote"
        /\ n \in req.recv
        /\ last_term[n] < req.term

        /\ last_term' = [last_term EXCEPT ![n] = req.term]
        /\ current_leader' = [current_leader EXCEPT ![n] = req.from]
        /\ msgs' = msgs \union buildVoteResponses(
                vote_logs, n, req, req.log_pos
            )

        /\ UNCHANGED committed_upper
        /\ UNCHANGED <<log, god_log>>
        /\ UNCHANGED leader_vars
        /\ UNCHANGED candidate_vars

---------------------------------------------------------------

compute_new_accept_pos(n, pos_map, log_len) ==
    LET
        non_inf_set(Q) == {n1 \in Q: pos_map[n1] # infinity /\ pos_map[n1] # nil}
        num_set(Q) == {pos_map[n1]: n1 \in non_inf_set(Q)}

        accept_pos_quorum(Q) ==
            IF num_set(Q) = {}
                THEN log_len
                ELSE MinOf(num_set(Q)) - 1

        all_quorums == {Q \in SUBSET members[n]: IsQuorum(n, Q)}
        result == {accept_pos_quorum(Q): Q \in all_quorums}
    IN
        MaxOf(result)

RECURSIVE buildAcceptRequests(_, _, _, _, _)

buildAcceptRequests(n, term, pos, max_pos, input_log) ==
    LET
        accept_req == [
            type |-> "AcceptEntry",
            term |-> term,
            from |-> n,
            log_pos |-> pos,
            entry |-> input_log[1],
            recv |-> members[n]
        ]
    IN
        IF pos <= max_pos
            THEN {accept_req} \union buildAcceptRequests(
                    n, term, pos + 1, max_pos, Tail(input_log)
                )
            ELSE {}



doHandleVoteResponse(n, resp) ==
    LET
        from == resp.from
        remain_pos == candidate_remain_pos[n][from]

        update_remain_pos ==
            IF resp.more
                THEN [candidate_remain_pos EXCEPT ![n][from] = @ + 1]
                ELSE [candidate_remain_pos EXCEPT ![n][from] = infinity]

        new_pos_map == update_remain_pos[n]

        mem_pos == resp.log_pos - last_committed[n]

        null_entry == [
            type |-> "Null",
            committed |-> FALSE,
            term |-> 20
        ]

        prev_entry == getLogEntryNull(mem_log[n], mem_pos)
        prev_term ==
            IF prev_entry = nil
                THEN 19
                ELSE prev_entry.term

        put_entry_tmp ==
            IF resp.entry = nil
                THEN null_entry
                ELSE resp.entry

        put_entry ==
            IF lessThanWithInf(prev_term, put_entry_tmp.term)
                THEN put_entry_tmp
                ELSE prev_entry

        update_mem_log ==
            /\ mem_log' = [mem_log EXCEPT
                    ![n] = putToSequence(mem_log[n], mem_pos, put_entry)
                ]
            /\ log_voted' = [log_voted EXCEPT
                    ![n] = putToSequence(log_voted[n], mem_pos, {})
                ]

        total_log_len == Len(mem_log'[n]) + last_committed[n]
        new_accept_pos == compute_new_accept_pos(n, new_pos_map, total_log_len)
        begin_accept_pos == candidate_accept_pos[n] + 1

        send_accept_req ==
            msgs' = msgs \union buildAcceptRequests(
                n, resp.term,
                begin_accept_pos,
                new_accept_pos,
                SubSeq(
                    mem_log'[n],
                    begin_accept_pos - last_committed[n],
                    Len(mem_log'[n])
                )
            )

        inf_set == {n1 \in DOMAIN new_pos_map: new_pos_map[n1] = infinity}
    IN
    /\ resp.type = "VoteResponse"
    /\ state[n] = "Candidate"
    /\ last_propose_term[n] = resp.term
    /\ remain_pos = resp.log_pos
    /\ resp.log_pos > candidate_accept_pos[n]

    /\ IF resp.more
        THEN update_mem_log
        ELSE
            /\ UNCHANGED mem_log
            /\ UNCHANGED log_voted

    /\ send_accept_req

    /\ IF IsQuorum(n, inf_set)
        THEN
            /\ state' = [state EXCEPT ![n] = "Leader"]
            /\ candidate_remain_pos' = [candidate_remain_pos EXCEPT ![n] = nil]
            /\ candidate_accept_pos' = [candidate_accept_pos EXCEPT ![n] = nil]
        ELSE
            /\ UNCHANGED state
            /\ candidate_remain_pos' = update_remain_pos
            /\ candidate_accept_pos' = [candidate_accept_pos
                    EXCEPT ![n] = new_accept_pos]

    /\ UNCHANGED last_propose_term
    /\ UNCHANGED global_last_term
    /\ UNCHANGED last_committed
    /\ UNCHANGED members
    /\ UNCHANGED acceptor_vars
    /\ UNCHANGED last_cmd_num
    /\ UNCHANGED god_log

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
    /\ log_voted' = [log_voted EXCEPT ![n] = Append(@, {})]
    /\ msgs' = msgs \union {accept_req}

    /\ UNCHANGED state
    /\ UNCHANGED candidate_vars
    /\ UNCHANGED last_propose_term
    /\ UNCHANGED global_last_term
    /\ UNCHANGED last_committed
    /\ UNCHANGED members
    /\ UNCHANGED acceptor_vars
    /\ UNCHANGED god_log


putToLog(n, entry, pos) ==
    LET
        new_log == putToSequence(log[n], pos, entry)
    IN
        [log EXCEPT ![n] = new_log]


doAcceptEntry(n, req) ==
    LET
        pos == req.log_pos

        resp == [
            type |-> "AcceptResponse",
            term |-> req.term,
            from |-> n,
            to |-> req.from,
            log_pos |-> pos
        ]

        put_entry ==
            IF pos <= committed_upper[n]
                THEN setLogCommittedEntry(req.entry)
                ELSE req.entry

        on_success ==
            /\ last_term' = [last_term EXCEPT ![n] = req.term]
            /\ current_leader' = [current_leader EXCEPT ![n] = req.from]
            /\ msgs' = msgs \union {resp}
            /\ log' = putToLog(n, put_entry, pos)

        fail_resp == [
            type |-> "AcceptFailed",
            term |-> last_term[n],
            to |-> req.from
        ]

        on_fail ==
            /\ fail_resp \notin msgs
            /\ msgs' = msgs \union {fail_resp}
            /\ UNCHANGED last_term
            /\ UNCHANGED current_leader
            /\ UNCHANGED log
    IN
    /\ req.type = "AcceptEntry"
    /\ n \in req.recv

    /\ IF req.term >= last_term[n]
        THEN on_success
        ELSE on_fail

    /\ UNCHANGED leader_vars
    /\ UNCHANGED god_log
    /\ UNCHANGED committed_upper
    /\ UNCHANGED candidate_vars

AcceptEntry(n) ==
    \E req \in msgs: doAcceptEntry(n, req)

---------------------------------------------------------------

RECURSIVE computeMaxCommitted(_)

computeMaxCommitted(input_log) ==
    IF Len(input_log) = 0 THEN
        0
    ELSE IF input_log[1].committed THEN
        1 + computeMaxCommitted(Tail(input_log))
    ELSE
        0

doHandleAcceptResponse(n, resp) ==
    LET
        pos == resp.log_pos - last_committed[n]
        old_votes == log_voted[n][pos]
        new_votes == old_votes \union {resp.from}

        is_quorum == IsQuorum(n, new_votes)

        update_voted ==
            [log_voted EXCEPT ![n][pos] = new_votes]

        update_log_committed ==
            IF is_quorum
                THEN setLogCommitted(mem_log, n, pos)
                ELSE mem_log

        move_forward == computeMaxCommitted(update_log_committed[n])

        update_last_committed ==
            last_committed' = [last_committed EXCEPT ![n] = @ + move_forward]

        truncate_seq(seq) ==
            [seq EXCEPT ![n] = SubSeq(@, move_forward + 1, Len(@))]

        commit_req == [
            type |-> "CommitLog",
            term |-> last_propose_term[n],
            log_pos |-> last_committed'[n],
            recv |-> members[n]
        ]

        send_commit_msg ==
            /\ msgs' = msgs \union {commit_req}
    IN
    /\ resp.type = "AcceptResponse"
    /\ resp.to = n
    /\ state[n] \in {"Candidate", "Leader"}
    /\ resp.term = last_propose_term[n]
    /\ resp.log_pos > last_committed[n]
    /\ resp.from \notin old_votes

    /\ update_last_committed
    /\ mem_log' = truncate_seq(update_log_committed)
    /\ log_voted' = truncate_seq(update_voted)
    /\ god_log' = AppendFrom(
            god_log,
            last_committed[n] + 1,
            SubSeq(update_log_committed[n], 1, move_forward)
        )

    /\ UNCHANGED msgs
    /\ UNCHANGED state
    /\ UNCHANGED members
    /\ UNCHANGED last_propose_term
    /\ UNCHANGED last_cmd_num
    /\ UNCHANGED global_last_term
    /\ UNCHANGED candidate_vars
    /\ UNCHANGED acceptor_vars

HandleAcceptResponse(n) ==
    \E resp \in msgs: doHandleAcceptResponse(n, resp)

---------------------------------------------------------------

doHandleAcceptFailed(n, resp) ==
    /\ resp.type = "AcceptFailed"
    /\ resp.term > last_propose_term[n]
    /\ state[n] \in {"Candidate", "Leader"}

    /\ state' = [state EXCEPT ![n] = "Follower"]
    /\ last_committed' = [last_committed EXCEPT ![n] = nil]
    /\ candidate_remain_pos' = [candidate_remain_pos EXCEPT ![n] = nil]
    /\ candidate_accept_pos' = [candidate_accept_pos EXCEPT ![n] = nil]
    /\ mem_log' = [mem_log EXCEPT ![n] = <<>>]
    /\ log_voted' = [log_voted EXCEPT ![n] = <<>>]

    /\ UNCHANGED last_propose_term
    /\ UNCHANGED global_last_term
    /\ UNCHANGED last_cmd_num
    /\ UNCHANGED acceptor_vars
    /\ UNCHANGED members
    /\ UNCHANGED msgs
    /\ UNCHANGED god_log

HandleAcceptFailed(n) ==
    \E resp \in msgs: doHandleAcceptFailed(n, resp)

---------------------------------------------------------------

SyncCommitPosition(n) ==
    LET
        l == current_leader[n]
        upper == committed_upper[n] + 1
        entry == getLogEntryNull(log[n], upper)
    IN
    /\ l # nil
    /\ last_term[n] = last_propose_term[l]
    /\ last_committed[l] # nil
    /\ committed_upper[n] < last_committed[l]

    /\ committed_upper' = [committed_upper EXCEPT ![n] = @ + 1]
    /\ IF entry # nil /\ entry.term = last_term[n]
        THEN log' = setLogCommitted(log, n, upper)
        ELSE UNCHANGED log

    /\ UNCHANGED god_log
    /\ UNCHANGED current_leader
    /\ UNCHANGED last_term
    /\ UNCHANGED leader_vars
    /\ UNCHANGED candidate_vars
    /\ UNCHANGED msgs

---------------------------------------------------------------

TerminateCond ==
    /\ global_last_term = max_term_num
    /\ \A n \in Node:
        /\ mem_log[n] = <<>>
        /\ state[n] \in {"Follower", "Leader"}
    /\ \A n \in Node:
        /\ ~(ENABLED SyncCommitPosition(n))
        /\ current_leader[n] # nil => committed_upper[n] = Len(god_log)

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
        \/ HandleAcceptResponse(n)
        \/ HandleAcceptFailed(n)
        \/ SyncCommitPosition(n)
    \/ Terminated

Spec == Init /\ [][Next]_vars

Sym == Permutations(Node)

---------------------------------------------------------------

MemLogMatchLogVoted ==
    \A n \in Node:
        Len(mem_log[n]) = Len(log_voted[n])


LogEntryCommittedInv ==
    \A n \in Node:
        \A i \in DOMAIN log[n]:
            LET
                e == log[n][i]

                is_committed ==
                    /\ e.committed
                    /\ e.term = infinity

                not_committed ==
                    /\ ~e.committed
                    /\ e.term # infinity
            IN
                e # nil =>
                    \/ is_committed
                    \/ not_committed

MemLogNonNilInv ==
    \A n \in Node: \A i \in DOMAIN mem_log[n]:
        LET
            e == mem_log[n][i]

            is_committed ==
                /\ e.committed
                /\ e.term = infinity

            not_committed ==
                /\ ~e.committed
                /\ e.term # infinity
        IN
        /\ e # nil
        /\ is_committed \/ not_committed


CandidateRemainPosInv ==
    \A n \in Node:
        candidate_remain_pos[n] # nil <=> state[n] = "Candidate"


GodLogConsistency ==
    \A n \in Node: \A i \in DOMAIN log[n]:
        LET
            e == log[n][i]
        IN
            e # nil /\ e.committed => god_log[i] = e

GodLogNoLost ==
    LET
        god_len == Len(god_log)
    IN
        \E n \in Node: Len(log[n]) >= god_len


GodLogInv ==
    \A i \in DOMAIN god_log:
        \/ god_log[i] # nil
        \/ god_log[i].committed

godLogNeverShrinkStep ==
    /\ Len(god_log') > Len(god_log)

GodLogNeverShrink ==
    [][godLogNeverShrinkStep]_god_log


MemLogNonEmptyInv ==
    LET
        is_active(n) == state[n] \in {"Candidate", "Leader"}
    IN
    \A n \in Node:
        /\ mem_log[n] # <<>> => is_active(n)
        /\ log_voted[n] # <<>> => is_active(n)
        /\ last_committed[n] # nil => is_active(n)


LogTermInv ==
    \A n1, n2 \in Node:
        LET
            len ==
                IF Len(log[n1]) > Len(log[n2])
                    THEN Len(log[n2])
                    ELSE Len(log[n1])
        IN
            \A i \in 1..len:
                LET
                    e1 == log[n1][i]
                    e2 == log[n2][i]
                    pre_cond ==
                        /\ e1 # nil
                        /\ e2 # nil
                        /\ e1.term = e2.term
                IN
                    pre_cond => e1 = e2

====

------ MODULE MultiPaxos ----
EXTENDS TLC, Utils

CONSTANTS Node, nil, infinity, max_start_election,
    total_num_cmd, max_member_change

-------------------------

putToSequence(seq, pos, x) ==
    PutToSequenceWithDefault(seq, pos, x, nil)

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
    log, last_term, acceptor_committed, current_leader,
    global_last_term,
    members, state, last_committed,
    last_propose_term,
    mem_log, log_voted,
    last_cmd_num, num_member_change,
    candidate_remain_pos, candidate_accept_pos,
    msgs, god_log,
    handling_msg

candidate_vars == <<
    candidate_remain_pos, candidate_accept_pos
>>

leader_vars == <<
    global_last_term,
    members, state, last_committed,
    last_propose_term,
    mem_log, log_voted,
    last_cmd_num, num_member_change
>>

acceptor_vars == <<
    log, last_term, acceptor_committed, current_leader
>>

vars == <<
    acceptor_vars,
    leader_vars,
    candidate_vars,
    msgs, god_log,
    handling_msg
>>

---------------------------------------------------------------

NullNode == Node \union {nil}

max_term_num == 20 + max_start_election
TermNum == 21..max_term_num
TermNumInf == TermNum \union {infinity}

LogPos == (0..20)
NullLogPos == LogPos \union {nil}
InfLogPos == NullLogPos \union {infinity}

max_cmd_num == 30 + total_num_cmd
CmdNum == 30..max_cmd_num

MemberInfo == [
    nodes: SUBSET Node,
    from: 2..(2 + total_num_cmd + max_member_change)
]

MemberList == SeqN(MemberInfo, 2)

LogEntry ==
    LET
        membership== [
            type: {"Member"},
            term: TermNumInf,
            nodes: MemberList
        ]

        null_entry == [
            type: {"Null"},
            term: TermNumInf \union {20}
        ]

        cmd_entry == [
            type: {"Cmd"},
            term: TermNumInf,
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


IsQuorum(local_members, Q, pos) ==
    LET
        cond(i)==
            pos >= local_members[i].from =>
                IsQuorumOf(local_members[i].nodes, Q)

        is_true_set == {
            cond(i): i \in DOMAIN local_members
        }
    IN
        is_true_set = {TRUE}


GetAllMembers(local_members, pos) ==
    LET
        get_nodes(i) ==
            IF pos >= local_members[i].from
                THEN local_members[i].nodes
                ELSE {}

        sub_list == {get_nodes(i): i \in DOMAIN local_members}
    IN
        UNION sub_list

---------------------------------------------------------------

InitTermNum == TermNum \union {20}

RemainPosition ==
    [Node -> InfLogPos] \union {nil}

TypeOKCheck ==
    /\ mem_log \in [Node -> Seq(LogEntry)]


TypeOK ==
    /\ log \in [Node -> Seq(NullLogEntry)]
    /\ last_term \in [Node -> InitTermNum]
    /\ acceptor_committed \in [Node -> LogPos]
    /\ current_leader \in [Node -> NullNode]
    /\ god_log \in Seq(NullLogEntry)

    /\ state \in [Node -> {"Follower", "Candidate", "Leader"}]
    /\ members \in [Node -> (MemberList \union {nil})]
    /\ last_committed \in [Node -> NullLogPos]
    /\ global_last_term \in InitTermNum
    /\ last_propose_term \in [Node -> InitTermNum]

    /\ mem_log \in [Node -> Seq(LogEntry)]
    /\ log_voted \in [Node -> Seq(SUBSET Node)]
    /\ last_cmd_num \in CmdNum
    /\ num_member_change \in 0..max_member_change

    /\ candidate_remain_pos \in [Node -> RemainPosition]
    /\ candidate_accept_pos \in [Node -> NullLogPos]

    /\ msgs \subseteq Message
    /\ handling_msg \in (Message \union {nil})

init_member_log ==
    \E S \in SUBSET Node:
        LET
            member_info == [
                nodes |-> S,
                from |-> 2
            ]

            init_entry == [
                type |-> "Member",
                term |-> infinity,
                nodes |-> <<member_info>>
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
        /\ log = [n \in Node |-> init_logs(n)]
        /\ acceptor_committed = [n \in Node |-> init_committed(n)]
        /\ god_log = <<init_entry>>

Init ==
    /\ init_member_log
    /\ members = [n \in Node |-> nil]
    /\ last_term = [n \in Node |-> 20]
    /\ current_leader = [n \in Node |-> nil]

    /\ state = [n \in Node |-> "Follower"]
    /\ last_committed = [n \in Node |-> nil]
    /\ global_last_term = 20
    /\ last_propose_term = [n \in Node |-> 20]

    /\ mem_log = [n \in Node |-> <<>>]
    /\ log_voted = [n \in Node |-> <<>>]
    /\ last_cmd_num = 30
    /\ num_member_change = 0

    /\ candidate_remain_pos = [n \in Node |-> nil]
    /\ candidate_accept_pos = [n \in Node |-> nil]

    /\ msgs = {}
    /\ handling_msg = nil

----------------------

setLogCommitted(input_log, n, pos) ==
    [input_log EXCEPT ![n][pos].term = infinity]

setLogCommittedEntry(entry) ==
    [entry EXCEPT !.term = infinity]

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

RECURSIVE computeCommittedInfoRecur(_)

(*
- obj.log
- obj.pos
- obj.members
*)
computeCommittedInfoRecur(obj) ==
    LET
        next_pos == obj.pos + 1
        entry == obj.log[next_pos]

        update_members ==
            IF entry.type = "Member"
                THEN entry.nodes
                ELSE obj.members

        new_obj == [obj EXCEPT
            !.pos = next_pos,
            !.members = update_members
        ]
    IN
        IF next_pos > Len(obj.log) THEN
            obj
        ELSE IF entry # nil /\ entry.term = infinity THEN
            computeCommittedInfoRecur(new_obj)
        ELSE
            obj

computeCommittedInfo(n) ==
    LET
        obj == [
            log |-> log[n],
            pos |-> 0,
            members |-> <<>>
        ]
    IN
        computeCommittedInfoRecur(obj)


StartElection(n) ==
    LET
        obj == computeCommittedInfo(n)
        commit_index == obj.pos
        pos == commit_index + 1
        all_members == GetAllMembers(obj.members, pos)

        req == [
            type |-> "RequestVote",
            from |-> n,
            term |-> last_propose_term'[n],
            log_pos |-> pos,
            recv |-> all_members
        ]

        init_remain_pos == [n1 \in Node |->
            IF n1 \in all_members
                THEN pos
                ELSE nil
        ]
    IN
    /\ n \in all_members
    /\ state[n] = "Follower"

    /\ global_last_term < max_term_num
    /\ global_last_term' = global_last_term + 1

    /\ state' = [state EXCEPT ![n] = "Candidate"]
    /\ last_propose_term' = [last_propose_term EXCEPT ![n] = global_last_term']
    /\ candidate_remain_pos' = [candidate_remain_pos EXCEPT ![n] = init_remain_pos]
    /\ candidate_accept_pos' = [candidate_accept_pos EXCEPT ![n] = commit_index]

    /\ msgs' = msgs \union {req}
    /\ last_committed' = [last_committed EXCEPT ![n] = commit_index]
    /\ members' = [members EXCEPT ![n] = obj.members]

    /\ UNCHANGED <<mem_log, log_voted>>
    /\ UNCHANGED acceptor_vars
    /\ UNCHANGED last_cmd_num
    /\ UNCHANGED god_log
    /\ UNCHANGED handling_msg
    /\ UNCHANGED num_member_change

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

        /\ handling_msg' = req
        /\ last_term' = [last_term EXCEPT ![n] = req.term]
        /\ current_leader' = [current_leader EXCEPT ![n] = req.from]
        /\ msgs' = msgs \union buildVoteResponses(
                vote_logs, n, req, req.log_pos
            )

        /\ UNCHANGED acceptor_committed
        /\ UNCHANGED <<log, god_log>>
        /\ UNCHANGED leader_vars
        /\ UNCHANGED candidate_vars

---------------------------------------------------------------

RECURSIVE handle_vote_response_recur(_)

(*
- obj.term
- obj.n
- obj.remain_map
- obj.mem_log
- obj.members
- obj.accept_pos
- obj.msgs
*)
handle_vote_response_recur(obj) ==
    LET
        pos == obj.accept_pos + 1

        remain_ok_set == {
            n1 \in Node:
                /\ obj.remain_map[n1] # nil
                /\ obj.remain_map[n1] # infinity => obj.remain_map[n1] > pos
        }

        mem_pos == pos - last_committed[obj.n]
        new_mem_log == [obj.mem_log EXCEPT ![mem_pos].term = obj.term]

        accept_req == [
            type |-> "AcceptEntry",
            term |-> obj.term,
            from |-> obj.n,
            log_pos |-> pos,
            entry |-> new_mem_log[mem_pos],
            recv |-> GetAllMembers(obj.members, pos)
        ]

        new_obj == [obj EXCEPT
            !.accept_pos = pos,
            !.mem_log = new_mem_log,
            !.msgs = @ \union {accept_req}
        ]
    IN
        IF mem_pos <= Len(obj.mem_log) /\ IsQuorum(obj.members, remain_ok_set, pos)
            THEN handle_vote_response_recur(new_obj)
            ELSE obj

doHandleVoteResponse(n, resp) ==
    LET
        from == resp.from
        remain_pos == candidate_remain_pos[n][from]
        term == last_propose_term[n]

        update_remain_map ==
            IF resp.more
                THEN [candidate_remain_pos[n] EXCEPT ![from] = @ + 1]
                ELSE [candidate_remain_pos[n] EXCEPT ![from] = infinity]

        mem_pos == resp.log_pos - last_committed[n]
        local_mem_log == mem_log[n]

        prev_entry == getLogEntryNull(local_mem_log, mem_pos)
        prev_term ==
            IF prev_entry = nil
                THEN 19
                ELSE prev_entry.term

        null_entry == [
            type |-> "Null",
            term |-> 20
        ]

        put_entry_tmp ==
            IF resp.entry = nil
                THEN null_entry
                ELSE resp.entry

        put_entry ==
            IF lessThanWithInf(prev_term, put_entry_tmp.term)
                THEN put_entry_tmp
                ELSE prev_entry

        update_mem_log ==
            IF resp.more THEN
                putToSequence(local_mem_log, mem_pos, put_entry)
            ELSE
                local_mem_log

        update_log_voted ==
            IF resp.more THEN
                putToSequence(log_voted[n], mem_pos, {})
            ELSE
                log_voted[n]

        obj == [
            term |-> term,
            n |-> n,
            members |-> members[n],
            remain_map |-> update_remain_map,
            mem_log |-> update_mem_log,
            accept_pos |-> candidate_accept_pos[n],
            msgs |-> msgs
        ]

        new_obj == handle_vote_response_recur(obj)

        inf_set == {n1 \in DOMAIN new_obj.remain_map:
            new_obj.remain_map[n1] = infinity
        }
        inf_check_pos == last_committed[n] + Len(new_obj.mem_log) + 1
    IN
    /\ resp.type = "VoteResponse"
    /\ state[n] = "Candidate"
    /\ last_propose_term[n] = resp.term
    /\ remain_pos = resp.log_pos
    /\ resp.log_pos > candidate_accept_pos[n]

    /\ handling_msg' = resp
    /\ mem_log' = [mem_log EXCEPT ![n] = new_obj.mem_log]
    /\ log_voted' = [log_voted EXCEPT ![n] = update_log_voted]
    /\ msgs' = new_obj.msgs

    /\ IF IsQuorum(members[n], inf_set, inf_check_pos)
        THEN
            /\ state' = [state EXCEPT ![n] = "Leader"]
            /\ candidate_remain_pos' = [candidate_remain_pos EXCEPT ![n] = nil]
            /\ candidate_accept_pos' = [candidate_accept_pos EXCEPT ![n] = nil]
        ELSE
            /\ UNCHANGED state
            /\ candidate_remain_pos' = [candidate_remain_pos
                    EXCEPT ![n] = new_obj.remain_map]
            /\ candidate_accept_pos' = [candidate_accept_pos
                    EXCEPT ![n] = new_obj.accept_pos]

    /\ UNCHANGED last_propose_term
    /\ UNCHANGED global_last_term
    /\ UNCHANGED last_committed
    /\ UNCHANGED members
    /\ UNCHANGED acceptor_vars
    /\ UNCHANGED last_cmd_num
    /\ UNCHANGED god_log
    /\ UNCHANGED num_member_change

HandleVoteResponse(n) ==
    \E resp \in msgs: doHandleVoteResponse(n, resp)

---------------------------------------------------------------

NewCommand(n) ==
    LET
        log_entry == [
            type |-> "Cmd",
            term |-> last_propose_term[n],
            cmd |-> last_cmd_num'
        ]

        log_pos == last_committed[n] + Len(mem_log'[n])

        accept_req == [
            type |-> "AcceptEntry",
            term |-> last_propose_term[n],
            from |-> n,
            log_pos |-> log_pos,
            entry |-> log_entry,
            recv |-> GetAllMembers(members[n], log_pos)
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
    /\ UNCHANGED handling_msg
    /\ UNCHANGED num_member_change

---------------------------------------------------------------

doChangeMembership(n, new_nodes) ==
    LET
        local_members == members[n]
        enable_cond ==
            \A i \in DOMAIN local_members:
                local_members[i].nodes # new_nodes

        pos == last_committed[n] + Len(mem_log[n]) + 1

        old_conf == local_members[1]
        new_conf == [
            nodes |-> new_nodes,
            from |-> pos + 1
        ]

        new_members == <<old_conf, new_conf>>

        log_entry == [
            type |-> "Member",
            term |-> last_propose_term[n],
            nodes |-> new_members
        ]

        accept_req == [
            type |-> "AcceptEntry",
            term |-> last_propose_term[n],
            from |-> n,
            log_pos |-> pos,
            entry |-> log_entry,
            recv |-> GetAllMembers(local_members, pos)
        ]
    IN
    /\ state[n] = "Leader"
    /\ new_nodes # {}
    /\ num_member_change < max_member_change
    /\ num_member_change' = num_member_change + 1
    /\ Len(local_members) = 1
    /\ enable_cond

    /\ members' = [members EXCEPT ![n] = new_members]
    /\ mem_log' = [mem_log EXCEPT ![n] = Append(@, log_entry)]
    /\ log_voted' = [log_voted EXCEPT ![n] = Append(@, {})]
    /\ msgs' = msgs \union {accept_req}

    /\ UNCHANGED state
    /\ UNCHANGED global_last_term
    /\ UNCHANGED god_log
    /\ UNCHANGED handling_msg
    /\ UNCHANGED last_committed
    /\ UNCHANGED candidate_vars
    /\ UNCHANGED acceptor_vars
    /\ UNCHANGED last_cmd_num
    /\ UNCHANGED last_propose_term

ChangeMembership(n) ==
    \E nodes \in (SUBSET Node): doChangeMembership(n, nodes)

---------------------------------------------------------------

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

        prev_entry == getLogEntryNull(log[n], pos)

        put_entry ==
            IF prev_entry # nil /\ prev_entry.term = infinity THEN
                prev_entry
            ELSE IF pos <= acceptor_committed[n] THEN
                setLogCommittedEntry(req.entry)
            ELSE
                req.entry

        new_log == putToSequence(log[n], pos, put_entry)

        on_success ==
            /\ last_term' = [last_term EXCEPT ![n] = req.term]
            /\ current_leader' = [current_leader EXCEPT ![n] = req.from]
            /\ msgs' = msgs \union {resp}
            /\ log' = [log EXCEPT ![n] = new_log]

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

    /\ handling_msg' = req
    /\ IF req.term >= last_term[n]
        THEN on_success
        ELSE on_fail

    /\ UNCHANGED leader_vars
    /\ UNCHANGED god_log
    /\ UNCHANGED acceptor_committed
    /\ UNCHANGED candidate_vars

AcceptEntry(n) ==
    \E req \in msgs: doAcceptEntry(n, req)

---------------------------------------------------------------

RECURSIVE computeMaxCommitted(_)

computeMaxCommitted(input_log) ==
    IF Len(input_log) = 0 THEN
        0
    ELSE IF input_log[1].term = infinity THEN
        1 + computeMaxCommitted(Tail(input_log))
    ELSE
        0

doHandleAcceptResponse(n, resp) ==
    LET
        pos == resp.log_pos - last_committed[n]
        old_votes == log_voted[n][pos]
        new_votes == old_votes \union {resp.from}

        is_quorum == IsQuorum(members[n], new_votes, resp.log_pos)

        update_voted ==
            [log_voted EXCEPT ![n][pos] = new_votes]

        update_log_committed ==
            IF is_quorum
                THEN setLogCommitted(mem_log, n, pos)
                ELSE mem_log

        accept_mem_pos == candidate_accept_pos[n] - last_committed[n]

        accept_log ==
            IF candidate_accept_pos[n] # nil
                THEN SubSeq(update_log_committed[n], 1, accept_mem_pos)
                ELSE update_log_committed[n]

        move_forward == computeMaxCommitted(accept_log)

        update_last_committed ==
            last_committed' = [last_committed EXCEPT ![n] = @ + move_forward]

        truncate_seq(seq) ==
            [seq EXCEPT ![n] = SubSeq(@, move_forward + 1, Len(@))]
    IN
    /\ resp.type = "AcceptResponse"
    /\ resp.to = n
    /\ state[n] \in {"Candidate", "Leader"}
    /\ resp.term = last_propose_term[n]
    /\ resp.log_pos > last_committed[n]
    /\ resp.from \notin old_votes

    /\ handling_msg' = resp
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
    /\ UNCHANGED num_member_change

HandleAcceptResponse(n) ==
    \E resp \in msgs: doHandleAcceptResponse(n, resp)

---------------------------------------------------------------

doHandleAcceptFailed(n, resp) ==
    /\ resp.type = "AcceptFailed"
    /\ resp.term > last_propose_term[n]
    /\ state[n] \in {"Candidate", "Leader"}

    /\ handling_msg' = resp
    /\ state' = [state EXCEPT ![n] = "Follower"]
    /\ last_committed' = [last_committed EXCEPT ![n] = nil]
    /\ candidate_remain_pos' = [candidate_remain_pos EXCEPT ![n] = nil]
    /\ candidate_accept_pos' = [candidate_accept_pos EXCEPT ![n] = nil]
    /\ mem_log' = [mem_log EXCEPT ![n] = <<>>]
    /\ log_voted' = [log_voted EXCEPT ![n] = <<>>]
    /\ members' = [members EXCEPT ![n] = nil]

    /\ UNCHANGED last_propose_term
    /\ UNCHANGED global_last_term
    /\ UNCHANGED last_cmd_num
    /\ UNCHANGED acceptor_vars
    /\ UNCHANGED msgs
    /\ UNCHANGED god_log
    /\ UNCHANGED num_member_change

HandleAcceptFailed(n) ==
    \E resp \in msgs: doHandleAcceptFailed(n, resp)

---------------------------------------------------------------

SyncLeaderCommitPosition(n) ==
    LET
        l == current_leader[n]
        upper == acceptor_committed[n] + 1
        entry == getLogEntryNull(log[n], upper)
    IN
    /\ l # nil
    /\ l = n
    /\ last_term[n] = last_propose_term[l]
    /\ last_committed[l] # nil
    /\ acceptor_committed[n] < last_committed[l]

    /\ acceptor_committed' = [acceptor_committed EXCEPT ![n] = @ + 1]
    /\ IF entry # nil /\ entry.term = last_term[n]
        THEN log' = setLogCommitted(log, n, upper)
        ELSE UNCHANGED log

    /\ UNCHANGED god_log
    /\ UNCHANGED current_leader
    /\ UNCHANGED last_term
    /\ UNCHANGED leader_vars
    /\ UNCHANGED candidate_vars
    /\ UNCHANGED msgs
    /\ UNCHANGED handling_msg

---------------------------------------------------------------

SyncCommitLogEntry(n) ==
    LET
        l == current_leader[n]
        obj == computeCommittedInfo(n)
        pos == obj.pos + 1
        local_log == log[n]

        leader_entry == getLogEntryNull(log[l], pos)

        inverse_cond ==
            /\ pos <= Len(local_log)
            /\ local_log[pos] # nil
            /\ local_log[pos].term = infinity
    IN
    /\ l # nil
    /\ last_term[n] = last_propose_term[l]
    /\ leader_entry # nil
    /\ leader_entry.term = infinity
    /\ ~inverse_cond

    /\ log' = [log EXCEPT ![n] = putToSequence(@, pos, leader_entry)]

    /\ UNCHANGED acceptor_committed
    /\ UNCHANGED god_log
    /\ UNCHANGED current_leader
    /\ UNCHANGED last_term
    /\ UNCHANGED leader_vars
    /\ UNCHANGED candidate_vars
    /\ UNCHANGED msgs
    /\ UNCHANGED handling_msg

---------------------------------------------------------------

logFullyReplicated ==
    LET
        obj == computeCommittedInfoRecur([
            log |-> god_log,
            pos |-> 0,
            members |-> <<>>
        ])
    IN
    \E Q \in SUBSET Node:
        /\ IsQuorum(obj.members, Q, 100)
        /\ \A n \in Q:
            computeCommittedInfo(n).pos = obj.pos

TerminateCond ==
    /\ global_last_term = max_term_num

    /\ \A n \in Node:
        /\ mem_log[n] = <<>>
        /\ state[n] \in {"Follower", "Leader"}
        /\ members[n] # nil =>
            /\ Len(members[n]) = 1
            /\ members[n][1].from = 2

    /\ logFullyReplicated

Terminated ==
    /\ TerminateCond
    /\ UNCHANGED vars

---------------------------------------

Next ==
    \/ \E n \in Node:
        \/ StartElection(n)
        \/ HandleRequestVote(n)
        \/ HandleVoteResponse(n)
        \/ NewCommand(n)
        \/ AcceptEntry(n)
        \/ ChangeMembership(n)
        \/ HandleAcceptResponse(n)
        \/ HandleAcceptFailed(n)
        \/ SyncLeaderCommitPosition(n)
        \/ SyncCommitLogEntry(n)
    \/ Terminated

Spec == Init /\ [][Next]_vars

Sym == Permutations(Node)

---------------------------------------------------------------

MemLogMatchLogVoted ==
    \A n \in Node:
        Len(mem_log[n]) = Len(log_voted[n])


CandidateRemainPosInv ==
    \A n \in Node:
        candidate_remain_pos[n] # nil <=> state[n] = "Candidate"


GodLogConsistency ==
    \A n \in Node: \A i \in DOMAIN log[n]:
        LET
            e == log[n][i]
        IN
            (e # nil /\ e.term = infinity) => god_log[i] = e

GodLogNoLost ==
    LET
        god_len == Len(god_log)
    IN
        \E n \in Node: Len(log[n]) >= god_len


GodLogInv ==
    \A i \in DOMAIN god_log:
        \/ god_log[i] # nil
        \/ god_log[i].term = infinity

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


AcceptRequestInv ==
    \A req \in msgs:
        req.type = "AcceptEntry" =>
            req.term = req.entry.term


MembersInv ==
    \A n \in Node:
        members[n] # nil <=> state[n] # "Follower"

---------------------------------------------------------------

MainNext == Next \* To ease navigating around

====

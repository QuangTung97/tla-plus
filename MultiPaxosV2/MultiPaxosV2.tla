---- MODULE MultiPaxosV2 ----
EXTENDS PaxosUtil

CONSTANTS Node, Value, nop, max_cmd_len, max_member_len

VARIABLES
    global_term,
    state, leader_term, mem_fully_repl, members_info,
    remain_map, prepare_log, mem_log, commit_log,
    msgs,
    acc_term, acc_log,
    god_log

leader_vars == <<
    global_term,
    state, leader_term, mem_fully_repl, members_info,
    remain_map, prepare_log, mem_log, commit_log,
    god_log
>>
acceptor_vars == <<acc_term, acc_log>>

vars == <<
    leader_vars,
    msgs,
    acceptor_vars
>>

------------------------------------------------------------------

Null(S) == S \union {nil}

Term == 20..29
InfTerm == Term \union {infinity}

LogPos == 0..6

InfLogPos == LogPos \union {infinity}

LeaderRemainMap == [Node -> Null(InfLogPos)]

-----------------------

NonEmptySubSet(S) == (SUBSET S) \ {{}}

MemberNodes == [
    nodes: NonEmptySubSet(Node),
    from: LogPos \ {0}
]

MembersInfo == FiniteSeq(MemberNodes, 1, 2)

LogValue ==
    LET
        cmdValue == [
            type: {"Cmd"},
            val: Value \union {nop}
        ]

        memberValue == [
            type: {"Membership"},
            members: MembersInfo
        ]
    IN
    UNION {cmdValue, memberValue}

newCmd(v) == [
    type |-> "Cmd",
    val |-> v
]

LogEntry == [
    term: InfTerm,
    value: LogValue
]

-----------------------

VoteReqMsg == [
    type: {"VoteReq"},
    term: Term,
    from_pos: LogPos,
    recv: NonEmptySubSet(Node)
]

VoteLogEntry == [
    term: Term,
    value: LogValue
]

VoteRespMsg == [
    type: {"VoteResp"},
    term: Term,
    from_node: Node,
    more: BOOLEAN,
    pos: LogPos,
    entry: Null(VoteLogEntry) \* (more = FALSE => entry = nil) (reverse not true)
]

AcceptReqMsg == [
    type: {"AcceptReq"},
    term: Term,
    pos: LogPos,
    value: LogValue,
    recv: NonEmptySubSet(Node)
]

AcceptRespMsg == [
    type: {"AcceptResp"},
    term: Term,
    from_node: Node,
    pos: LogPos
]

IsValidMsgSet(set) ==
    \A m \in set:
        \/ m \in VoteReqMsg
        \/ m \in VoteRespMsg
        \/ m \in AcceptReqMsg
        \/ m \in AcceptRespMsg

-----------------------

MemLogEntry == [
    value: LogValue,
    acceptors: SUBSET Node,
    committed: BOOLEAN
]

------------------------------------------------------------------

init_member_nodes(nodes) == [
    nodes |-> nodes,
    from |-> 1
]

init_log_value(nodes) == [
    type |-> "Membership",
    members |-> <<init_member_nodes(nodes)>>
]

init_log_entry(nodes) == [
    term |-> infinity,
    value |-> init_log_value(nodes)
]

------------------------------------------------------------------

TypeOK ==
    /\ global_term \in Term

    /\ state \in [Node -> {"Follower", "Candidate", "Leader"}]
    /\ leader_term \in [Node -> Term]
    /\ mem_fully_repl \in [Node -> Null(LogPos)]
    /\ members_info \in [Node -> Null(MembersInfo)]
    /\ remain_map \in [Node -> Null(LeaderRemainMap)]
    /\ prepare_log \in [Node -> Seq(VoteLogEntry)]
    /\ mem_log \in [Node -> Seq(MemLogEntry)]
    /\ commit_log \in [Node -> Seq(LogValue)]

    /\ IsValidMsgSet(msgs)

    /\ acc_term \in [Node -> Term]
    /\ acc_log \in [Node -> Seq(Null(LogEntry))]
    /\ god_log \in Seq(LogValue)

Init ==
    /\ global_term = 20

    /\ state = [n \in Node |-> "Follower"]
    /\ leader_term = [n \in Node |-> 20]
    /\ mem_fully_repl = [n \in Node |-> nil]
    /\ members_info = [n \in Node |-> nil]
    /\ remain_map = [n \in Node |-> nil]
    /\ prepare_log = [n \in Node |-> <<>>]
    /\ mem_log = [n \in Node |-> <<>>]
    /\ commit_log = [n \in Node |-> <<>>]

    /\ msgs = {}

    /\ acc_term = [n \in Node |-> 20]
    /\ \E nodes \in NonEmptySubSet(Node):
        /\ acc_log = [n \in Node |-> <<init_log_entry(nodes)>>]
        /\ god_log = <<init_log_value(nodes)>>

------------------------------------------------------------------

acceptor_fully_replicated(n) ==
    LET
        pred(e) ==
            IF e = nil
                THEN TRUE
                ELSE e.term # infinity
    IN
        FindFirstIndex(acc_log[n], pred) - 1

-----------------------

log_to_values(input_log) ==
    MapSeq(input_log, LAMBDA e: e.value)

RECURSIVE latest_members_info(_, _)

latest_members_info(current_info, input_values) ==
    LET
        v == input_values[1]
        is_members == v.type = "Membership"
        new_info == v.members
    IN
    IF Len(input_values) = 0 THEN
        current_info
    ELSE IF is_members THEN
        latest_members_info(new_info, Tail(input_values))
    ELSE
        latest_members_info(current_info, Tail(input_values))

-----------------------

RECURSIVE is_quorum_of_members(_, _, _)

is_quorum_of_members(nodes, pos, input_members) ==
    LET
        e == input_members[1]
        success ==
            pos >= e.from =>
                \E S \in QuorumOf(e.nodes): S \subseteq nodes
    IN
    IF Len(input_members) = 0 THEN
        TRUE
    ELSE IF success THEN
        is_quorum_of_members(nodes, pos, Tail(input_members))
    ELSE
        FALSE

is_quorum_of(n, nodes, pos) == \* TODO check usage
    is_quorum_of_members(nodes, pos, members_info[n])

-----------------------

RECURSIVE all_nodes_of_members(_, _)

all_nodes_of_members(result, input_members) ==
    LET
        e == input_members[1]
        new_result == result \union e.nodes
    IN
    IF Len(input_members) = 0
        THEN result
        ELSE all_nodes_of_members(new_result, Tail(input_members))

all_nodes_of(n) == \* TODO check usage
    all_nodes_of_members({}, members_info[n])

-----------------------

StartElection(n) ==
    LET
        fully_replicated == acceptor_fully_replicated(n)

        start_pos == fully_replicated + 1

        fully_log == SubSeq(acc_log[n], 1, fully_replicated)
        new_members == latest_members_info(nil, log_to_values(fully_log))
        all_nodes == all_nodes_of_members({}, new_members)

        vote_req == [
            type |-> "VoteReq",
            term |-> leader_term'[n],
            from_pos |-> start_pos,
            recv |-> all_nodes
        ]

        init_remain_pos(y) ==
            IF y \in all_nodes
                THEN start_pos
                ELSE nil

        new_remain_map == [y \in Node |-> init_remain_pos(y)]
    IN
    /\ state[n] = "Follower"
    /\ n \in all_nodes

    /\ global_term' = global_term + 1
    /\ leader_term' = [leader_term EXCEPT ![n] = global_term']
    /\ mem_fully_repl' = [mem_fully_repl EXCEPT ![n] = fully_replicated]
    /\ state' = [state EXCEPT ![n] = "Candidate"]
    /\ msgs' = msgs \union {vote_req}
    /\ remain_map' = [remain_map EXCEPT ![n] = new_remain_map]
    /\ members_info' = [members_info EXCEPT ![n] = new_members]

    /\ UNCHANGED <<prepare_log, mem_log, commit_log, god_log>>
    /\ UNCHANGED acceptor_vars

-----------------------

entry_with_default_nop(entry) ==
    IF entry = nil
        THEN [term |-> 20, value |-> newCmd(nop)] \* smallest possible term
        ELSE entry

end_commit_pos(n) ==
    mem_fully_repl[n] + Len(commit_log[n])

end_mem_pos(n) ==
    end_commit_pos(n) + Len(mem_log[n])

end_prepare_log(n) ==
    end_mem_pos(n) + Len(prepare_log[n])

-----------------------

RECURSIVE start_non_proposed_entry_index(_, _, _, _)

\* TODO delete
start_non_proposed_entry_index(n, pos, input_remain_map, input_prepare_log) ==
    LET
        entry == input_prepare_log[1]
        acceptors == {y \in all_nodes_of(n): log_pos_less(pos, input_remain_map[y])}
        is_proposed == is_quorum_of(n, acceptors, pos)
    IN
    IF Len(input_prepare_log) = 0 THEN
        1
    ELSE IF is_proposed THEN
        1 + start_non_proposed_entry_index(
            n, pos + 1, input_remain_map, Tail(input_prepare_log)
        )
    ELSE
        1

-----------------------

\* state includes:
\* - pos
\* - remain_map
\* - prepare_log
\* - mem_log
\* - members_info

RECURSIVE move_from_prepare_log_to_mem_log(_)

move_from_prepare_log_to_mem_log(st) ==
    LET
        e == st.prepare_log[1]

        all_nodes == all_nodes_of_members({}, st.members_info)
        acceptors == {y \in all_nodes: log_pos_less(st.pos, st.remain_map[y])}

        is_moved == is_quorum_of_members(acceptors, st.pos, st.members_info)

        new_members_info ==
            IF e.value.type = "Membership"
                THEN e.value.members
                ELSE st.members_info

        new_state == [st EXCEPT
            !.pos = @ + 1,
            !.prepare_log = Tail(@),
            !.mem_log = Append(st.mem_log, e.value),
            !.members_info = new_members_info
        ]
    IN
    IF Len(st.prepare_log) > 0 /\ is_moved THEN
        move_from_prepare_log_to_mem_log(new_state)
    ELSE
        st

-----------------------

remain_pos_is_number(pos) ==
    /\ pos # nil
    /\ pos # infinity

\* set all remain pos to be >= new_start_pos
set_remain_map_not_less_than(new_remain_map, new_start_pos) ==
    LET
        update_final_pos(old_pos) ==
            IF remain_pos_is_number(old_pos) /\ old_pos < new_start_pos
                THEN new_start_pos
                ELSE old_pos
    IN
        [n \in DOMAIN new_remain_map |-> update_final_pos(new_remain_map[n])]

-----------------------

append_mem_log(n, values, members) ==
    LET
        new_entry_fn(v) == [
            value |-> v,
            acceptors |-> {},
            committed |-> FALSE
        ]
        entry_list == MapSeq(values, new_entry_fn)

        compute_pos(i) == end_mem_pos(n) + i

        all_nodes == all_nodes_of_members({}, members)

        acc_req(i, v) == [
            type |-> "AcceptReq",
            term |-> leader_term[n],
            pos |-> compute_pos(i),
            value |-> v,
            recv |-> all_nodes
        ]

        acc_req_set == {
            acc_req(i, values[i]): i \in DOMAIN values
        }
    IN
    /\ mem_log' = [mem_log EXCEPT ![n] = @ \o entry_list]
    /\ msgs' = msgs \union acc_req_set

-----------------------

doHandleVoteResp(n, resp) ==
    LET
        y == resp.from_node

        old_remain_map == remain_map[n]
        new_remain_map ==
            IF resp.more
                THEN [old_remain_map EXCEPT ![y] = @ + 1]
                ELSE [old_remain_map EXCEPT ![y] = infinity]

        \* put entry to prepare_log
        index == resp.pos - end_mem_pos(n)

        prev_entry == entry_with_default_nop(GetSeqPos(prepare_log[n], index))
        resp_entry == entry_with_default_nop(resp.entry)
        put_entry ==
            IF prev_entry.term > resp_entry.term
                THEN prev_entry
                ELSE resp_entry

        old_prepare_log == prepare_log[n]
        put_prepare_log ==
            IF resp.more
                THEN PutSeqPos(old_prepare_log, index, put_entry)
                ELSE old_prepare_log

        \* move from prepare_log to mem_log
        move_state == [
            pos |-> end_mem_pos(n) + 1,
            remain_map |-> new_remain_map,
            prepare_log |-> put_prepare_log,
            mem_log |-> <<>>,
            members_info |-> members_info[n]
        ]
        result_state == move_from_prepare_log_to_mem_log(move_state)

        final_remain_map == set_remain_map_not_less_than(
            new_remain_map, result_state.pos
        )

        \* check become leader
        inf_set == {x \in all_nodes_of(n): final_remain_map[x] = infinity}

        switch_to_leader == is_quorum_of_members(
            inf_set, result_state.pos, result_state.members_info
        )

        when_become_leader ==
            /\ state' = [state EXCEPT ![n] = "Leader"]
            /\ remain_map' = [remain_map EXCEPT ![n] = nil]

        when_normal ==
            /\ remain_map' = [remain_map EXCEPT ![n] = final_remain_map]
            /\ UNCHANGED state
    IN
    /\ state[n] = "Candidate"
    /\ remain_map[n][y] = resp.pos

    /\ prepare_log' = [prepare_log EXCEPT ![n] = result_state.prepare_log]
    /\ append_mem_log(n, result_state.mem_log, result_state.members_info)
    /\ members_info' = [members_info EXCEPT ![n] = result_state.members_info]

    /\ IF switch_to_leader
        THEN when_become_leader
        ELSE when_normal

    /\ UNCHANGED <<leader_term, mem_fully_repl, commit_log, god_log>>
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
        final_pos ==
            IF req.from_pos > Len(acc_log[n])
                THEN req.from_pos
                ELSE Len(acc_log[n]) + 1

        final_resp == [
            type |-> "VoteResp",
            term |-> req.term,
            from_node |-> n,
            more |-> FALSE,
            pos |-> final_pos,
            entry |-> nil
        ]

        log_entry(i) ==
            LET e == acc_log[n][i] IN
            IF e # nil /\ e.term = infinity
                THEN [e EXCEPT !.term = req.term]
                ELSE e

        normal_resp(i) == [final_resp EXCEPT
            !.more = TRUE,
            !.pos = i,
            !.entry = log_entry(i)
        ]

        resp_pos_set == {i \in DOMAIN acc_log[n]: i >= req.from_pos}
        normal_resp_set == {normal_resp(i): i \in resp_pos_set}
    IN
    /\ req.term > acc_term[n]
    /\ acc_term' = [acc_term EXCEPT ![n] = req.term]
    /\ msgs' = msgs \union normal_resp_set \union {final_resp}
    /\ UNCHANGED acc_log
    /\ UNCHANGED leader_vars

HandleVoteReq(n) ==
    \E req \in msgs:
        /\ req.type = "VoteReq"
        /\ n \in req.recv
        /\ doHandleVoteReq(n, req)

------------------------------------------------------------------

candidate_vars == <<prepare_log, state, leader_term, global_term, remain_map>>

leader_commit_log_values(n) ==
    LET
        fully_repl == mem_fully_repl[n]
        acc_log_entries == SubSeq(acc_log[n], 1, fully_repl)
        acc_log_values == log_to_values(acc_log_entries)
    IN
        acc_log_values \o commit_log[n]

num_entries_by_type(n, cmd_type) ==
    LET
        mem_values == log_to_values(mem_log[n])
        values == leader_commit_log_values(n) \o mem_values
        cmd_set == {pos \in DOMAIN values: values[pos].type = cmd_type}
    IN
        Cardinality(cmd_set)

doLeaderNewCmd(n, v) ==
    /\ state[n] = "Leader"
    /\ num_entries_by_type(n, "Cmd") < max_cmd_len
    /\ append_mem_log(n, <<newCmd(v)>>, members_info[n])
    /\ UNCHANGED <<mem_fully_repl, members_info, commit_log, god_log>>
    /\ UNCHANGED candidate_vars
    /\ UNCHANGED acceptor_vars

LeaderNewCmd(n) ==
    \E v \in Value: doLeaderNewCmd(n, v)

------------------------------------------------------------------

doChangeMembers(n, nodes) ==
    LET
        new_nodes_entry == [
            nodes |-> nodes,
            from |-> end_mem_pos(n) + 1
        ]

        new_members == Append(members_info[n], new_nodes_entry)

        cmd == [
            type |-> "Membership",
            members |-> new_members
        ]
    IN
    /\ state[n] = "Leader"
    /\ Len(members_info[n]) <= 1
    /\ num_entries_by_type(n, "Membership") < max_member_len

    /\ append_mem_log(n, <<cmd>>, new_members)
    /\ members_info' = [members_info EXCEPT ![n] = new_members]

    /\ UNCHANGED <<mem_fully_repl, commit_log, god_log>>
    /\ UNCHANGED candidate_vars
    /\ UNCHANGED acceptor_vars

LeaderChangeMembers(n) ==
    \E nodes \in NonEmptySubSet(Node):
        doChangeMembers(n, nodes)

------------------------------------------------------------------

FinishChangeMembers(n) ==
    LET
        old_members == members_info[n]
        from_pos == old_members[2].from

        tmp_members == Tail(old_members)
        new_members == [tmp_members EXCEPT ![1].from = 1]

        cmd == [
            type |-> "Membership",
            members |-> new_members
        ]
    IN
    /\ state[n] = "Leader"
    /\ Len(members_info[n]) > 1
    /\ from_pos <= end_commit_pos(n)

    /\ append_mem_log(n, <<cmd>>, new_members)
    /\ members_info' = [members_info EXCEPT ![n] = new_members]

    /\ UNCHANGED <<mem_fully_repl, commit_log, god_log>>
    /\ UNCHANGED candidate_vars
    /\ UNCHANGED acceptor_vars

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

        acc_resp == [
            type |-> "AcceptResp",
            term |-> req.term,
            pos |-> pos,
            from_node |-> n
        ]
    IN
    /\ req.term >= acc_term[n]
    /\ prev_entry # new_entry
    /\ acc_term' = [acc_term EXCEPT ![n] = req.term]
    /\ acc_log' = [acc_log EXCEPT ![n] = PutSeqPos(@, pos, new_entry)] \* TODO
    /\ msgs' = msgs \union {acc_resp}
    /\ UNCHANGED leader_vars

HandleAcceptReq(n) ==
    \E req \in msgs:
        /\ req.type = "AcceptReq"
        /\ n \in req.recv
        /\ doHandleAcceptReq(n, req)

------------------------------------------------------------------

doHandleAcceptResp(n, resp) ==
    LET
        pos == resp.pos
        y == resp.from_node
        index == pos - end_commit_pos(n)

        new_mem_log == [mem_log EXCEPT ![n][index].acceptors = @ \union {y}]

        is_committed ==
            is_quorum_of(n, new_mem_log[n][index].acceptors, pos)

        set_committed == [new_mem_log EXCEPT ![n][index].committed = is_committed]
        new_log == set_committed[n]

        first_non_commit == FindFirstIndex(new_log, LAMBDA entry: ~entry.committed)

        new_committed == SubSeq(new_log, 1, first_non_commit - 1)
        new_committed_values == log_to_values(new_committed)
    IN
    /\ state[n] \in {"Candidate", "Leader"}
    /\ pos > end_commit_pos(n)
    /\ y \notin mem_log[n][index].acceptors

    /\ mem_log' = [set_committed EXCEPT ![n] = RemoveSeqBefore(@, first_non_commit)]
    /\ commit_log' = [commit_log EXCEPT ![n] = @ \o new_committed_values]

    /\ IF mem_fully_repl[n] + Len(commit_log'[n]) > Len(god_log)
        THEN god_log' = SubSeq(god_log, 1, mem_fully_repl[n]) \o commit_log'[n]
        ELSE UNCHANGED god_log

    /\ UNCHANGED msgs
    /\ UNCHANGED <<mem_fully_repl, members_info>>
    /\ UNCHANGED <<leader_term, global_term, state, prepare_log, remain_map>>
    /\ UNCHANGED acceptor_vars

HandleAcceptResp(n) ==
    \E resp \in msgs:
        /\ resp.type = "AcceptResp"
        /\ resp.term = leader_term[n]
        /\ doHandleAcceptResp(n, resp)

------------------------------------------------------------------

doReplicateCommittedEntry(n, l) ==
    LET
        pos == acceptor_fully_replicated(n) + 1

        commit_index == pos - mem_fully_repl[l]

        leader_val ==
            IF pos <= mem_fully_repl[l]
                THEN acc_log[l][pos].value
                ELSE commit_log[l][commit_index]

        entry == [
            term |-> infinity,
            value |-> leader_val
        ]
    IN
    /\ pos <= end_commit_pos(l)
    /\ acc_log' = [acc_log EXCEPT ![n] = PutSeqPos(@, pos, entry)]

    /\ UNCHANGED acc_term
    /\ UNCHANGED leader_vars
    /\ UNCHANGED msgs

ReplicateCommittedEntry(n) ==
    \E l \in Node:
        /\ leader_term[l] = acc_term[n]
        /\ state[l] \in {"Leader", "Candidate"}
        /\ doReplicateCommittedEntry(n, l)

------------------------------------------------------------------

TerminateCond ==
    LET
        is_max_term(n) ==
            \A y \in Node: leader_term[n] >= leader_term[y]

        l == CHOOSE n \in Node: is_max_term(n)
    IN
    /\ state[l] = "Leader"
    /\ prepare_log[l] = <<>>
    /\ mem_log[l] = <<>>
    /\ Len(god_log) = max_cmd_len + (max_member_len - 1) * 2 + 1
    /\ Len(members_info[l]) = 1

Terminated ==
    /\ TerminateCond
    /\ UNCHANGED vars

-----------------------

Next ==
    \/ \E n \in Node:
        \/ StartElection(n)
        \/ HandleVoteReq(n)
        \/ HandleVoteResp(n)

        \/ LeaderNewCmd(n)
        \/ LeaderChangeMembers(n)
        \/ FinishChangeMembers(n)

        \/ HandleAcceptReq(n)
        \/ HandleAcceptResp(n)
        \/ ReplicateCommittedEntry(n)
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
        LET
            god_values == SubSeqSafe(god_log, 1, end_commit_pos(n))
            cond ==
                leader_commit_log_values(n) = god_values
        IN
            state[n] \in {"Leader", "Candidate"} => cond


NonCandidateStateInv ==
    LET
        cond(n) ==
            /\ prepare_log[n] = <<>>
            /\ remain_map[n] = nil
    IN
    \A n \in Node:
        state[n] # "Candidate" => cond(n)


start_prepare_pos(n) ==
    end_mem_pos(n) + 1

leader_candidate_inv_cond(n) ==
    /\ mem_fully_repl[n] # nil
    /\ members_info[n] # nil

CandidateStateInv ==
    LET
        non_proposed_index(n) ==
            start_non_proposed_entry_index(
                n, start_prepare_pos(n), remain_map[n], prepare_log[n]
            )

        cond(n) ==
            /\ non_proposed_index(n) = 1
            /\ leader_candidate_inv_cond(n)
            /\ \A y \in Node:
                y \in all_nodes_of(n) <=> remain_map[n][y] # nil
            /\ \A y \in all_nodes_of(n):
                remain_map[n][y] # infinity =>
                    /\ remain_map[n][y] # nil
                    /\ remain_map[n][y] >= start_prepare_pos(n)
    IN
    \A n \in Node:
        state[n] = "Candidate" => cond(n)


FollowerStateInv ==
    LET
        cond(n) ==
            /\ remain_map[n] = nil
            /\ mem_log[n] = <<>>
            /\ prepare_log[n] = <<>>
            /\ commit_log[n] = <<>>
            /\ mem_fully_repl[n] = nil
            /\ members_info[n] = nil
    IN
    \A n \in Node:
        state[n] = "Follower" => cond(n)


LeaderStateInv ==
    LET
        cond(n) ==
            /\ remain_map[n] = nil
            /\ prepare_log[n] = <<>>
            /\ leader_candidate_inv_cond(n)
    IN
    \A n \in Node:
        state[n] = "Leader" => cond(n)


InversedInv ==
    Len(god_log) = 0


\* TODO add invariant mem_log and members_info
\* TODO add property eventually state = Leader and mem_log = <<>>
\* TODO allow to disable a Node mid way

====

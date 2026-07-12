---- MODULE MultiPaxosV2 ----
EXTENDS PaxosUtil

CONSTANTS Node, Value, nop, max_cmd_len, max_member_len

ASSUME max_member_len >= 1

VARIABLES
    global_term,
    state, leader_term, mem_fully_repl, members_info,
    remain_map, prepare_log, mem_log, commit_log,
    vote_req_msgs, vote_resp_msgs, acc_req_msgs, acc_resp_msgs,
    acc_term, acc_log,
    term_all_nodes,
    god_log

leader_vars == <<
    global_term,
    state, leader_term, mem_fully_repl, members_info,
    remain_map, prepare_log, mem_log, commit_log,
    god_log
>>

acceptor_vars == <<acc_term, acc_log>>

msg_vars == <<vote_req_msgs, vote_resp_msgs, acc_req_msgs, acc_resp_msgs>>

vars == <<
    leader_vars,
    msg_vars,
    term_all_nodes,
    acceptor_vars
>>

------------------------------------------------------------------

Null(S) == S \union {nil}

max_term_num == 20 + Cardinality(Node)
Term == 20..max_term_num
NonZeroTerm == Term \ {20}
InfTerm == NonZeroTerm \union {infinity}

LogPos == 0..9

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
    term: Term
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
    value: LogValue
]

AcceptRespMsg == [
    type: {"AcceptResp"},
    term: Term,
    from_node: Node,
    pos: LogPos
]

-----------------------

MemLogEntry == [
    value: LogValue,
    acceptors: SUBSET Node
]

-----------------------

TermNodes == [
    all_nodes: SUBSET Node,
    from_pos: LogPos
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

init_term_nodes == [
    all_nodes |-> {},
    from_pos |-> 0
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

    /\ vote_req_msgs \subseteq VoteReqMsg
    /\ vote_resp_msgs \subseteq VoteRespMsg
    /\ acc_req_msgs \subseteq AcceptReqMsg
    /\ acc_resp_msgs \subseteq AcceptRespMsg

    /\ acc_term \in [Node -> Term]
    /\ acc_log \in [Node -> Seq(Null(LogEntry))]
    /\ god_log \in Seq(LogValue)

    /\ term_all_nodes \in [NonZeroTerm -> TermNodes]

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

    /\ vote_req_msgs = {}
    /\ vote_resp_msgs = {}
    /\ acc_req_msgs = {}
    /\ acc_resp_msgs = {}

    /\ acc_term = [n \in Node |-> 20]
    /\ \E nodes \in NonEmptySubSet(Node):
        /\ acc_log = [n \in Node |-> <<init_log_entry(nodes)>>]
        /\ god_log = <<init_log_value(nodes)>>

    /\ term_all_nodes = [t \in NonZeroTerm |-> init_term_nodes]

------------------------------------------------------------------

acceptor_fully_replicated_input_log(input_acc_log) ==
    LET
        pred(e) ==
            IF e = nil
                THEN TRUE
                ELSE e.term # infinity
    IN
        FindFirstIndex(input_acc_log, pred) - 1

acceptor_fully_replicated(n) ==
    acceptor_fully_replicated_input_log(acc_log[n])

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

RECURSIVE is_quorum_of_members(_, _)

is_quorum_of_members(nodes, input_members) ==
    LET
        e == input_members[1]
        success ==
            \E S \in QuorumOf(e.nodes): S \subseteq nodes
    IN
    IF Len(input_members) = 0 THEN
        TRUE
    ELSE IF success THEN
        is_quorum_of_members(nodes, Tail(input_members))
    ELSE
        FALSE

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
            term |-> leader_term'[n]
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
    /\ vote_req_msgs' = vote_req_msgs \union {vote_req}
    /\ remain_map' = [remain_map EXCEPT ![n] = new_remain_map]
    /\ members_info' = [members_info EXCEPT ![n] = new_members]

    /\ UNCHANGED <<vote_resp_msgs, acc_req_msgs, acc_resp_msgs>>
    /\ UNCHANGED <<prepare_log, mem_log, commit_log, god_log>>
    /\ UNCHANGED acceptor_vars
    /\ UNCHANGED term_all_nodes

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

        is_moved == is_quorum_of_members(acceptors, st.members_info)

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

\* set all remain pos to be >= new_start_pos
set_remain_map_not_less_than(new_remain_map, new_start_pos, input_all_nodes) ==
    LET
        update_final_pos(n, old_pos) ==
            IF n \notin input_all_nodes THEN
                nil
            ELSE IF old_pos = nil THEN
                new_start_pos
            ELSE IF old_pos = infinity THEN
                old_pos
            ELSE IF old_pos < new_start_pos THEN
                new_start_pos
            ELSE
                old_pos
    IN
        [n \in DOMAIN new_remain_map |-> update_final_pos(n, new_remain_map[n])]

-----------------------

append_mem_log_result(n, values) ==
    LET
        new_entry_fn(v) == [
            value |-> v,
            acceptors |-> {}
        ]
        entry_list == MapSeq(values, new_entry_fn)

        compute_pos(i) == end_mem_pos(n) + i

        acc_req(i, v) == [
            type |-> "AcceptReq",
            term |-> leader_term[n],
            pos |-> compute_pos(i),
            value |-> v
        ]

        acc_req_set == {
            acc_req(i, values[i]): i \in DOMAIN values
        }
    IN [
        mem_log |-> entry_list,
        acc_req |-> acc_req_set
    ]

append_mem_log(n, values) ==
    LET
        result == append_mem_log_result(n, values)
    IN
    /\ mem_log' = [mem_log EXCEPT ![n] = @ \o result.mem_log]
    /\ acc_req_msgs' = acc_req_msgs \union result.acc_req

-----------------------

move_from_mem_log_to_commit_log(input_log, input_members) ==
    LET
        is_quorum(entry) ==
            is_quorum_of_members(entry.acceptors, input_members)

        first_non_commit == FindFirstIndex(
            input_log, LAMBDA entry: ~is_quorum(entry)
        )

        new_committed == SubSeq(input_log, 1, first_non_commit - 1)
        new_committed_values == log_to_values(new_committed)
    IN [
        mem_log |-> RemoveSeqBefore(input_log, first_non_commit),
        commit_log |-> new_committed_values
    ]

-----------------------

append_commit_log(n, values) ==
    /\ commit_log' = [commit_log EXCEPT ![n] = @ \o values]
    /\ IF mem_fully_repl[n] + Len(commit_log'[n]) > Len(god_log)
        THEN god_log' = SubSeq(god_log, 1, mem_fully_repl[n]) \o commit_log'[n]
        ELSE UNCHANGED god_log

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

        old_all_nodes == all_nodes_of_members({}, move_state.members_info)
        new_all_nodes == all_nodes_of_members({}, result_state.members_info)

        final_remain_map == set_remain_map_not_less_than(
            new_remain_map, result_state.pos, new_all_nodes
        )

        \* check become leader
        inf_set == {x \in new_all_nodes: final_remain_map[x] = infinity}

        switch_to_leader == is_quorum_of_members(
            inf_set, result_state.members_info
        )

        when_become_leader ==
            /\ state' = [state EXCEPT ![n] = "Leader"]
            /\ remain_map' = [remain_map EXCEPT ![n] = nil]

        when_normal ==
            /\ remain_map' = [remain_map EXCEPT ![n] = final_remain_map]
            /\ UNCHANGED state

        new_vote_req == [
            type |-> "VoteReq",
            term |-> leader_term[n],
            from_pos |-> result_state.pos,
            recv |-> new_all_nodes
        ]
    IN
    /\ state[n] = "Candidate"
    /\ remain_map[n][y] = resp.pos

    /\ prepare_log' = [prepare_log EXCEPT ![n] = result_state.prepare_log]
    /\ append_mem_log(n, result_state.mem_log)
    /\ members_info' = [members_info EXCEPT ![n] = result_state.members_info]

    /\ IF new_all_nodes \ old_all_nodes = {}
        THEN UNCHANGED vote_req_msgs
        ELSE vote_req_msgs' = vote_req_msgs \union {new_vote_req}

    /\ IF switch_to_leader
        THEN when_become_leader
        ELSE when_normal

    /\ UNCHANGED <<vote_resp_msgs, acc_resp_msgs>>
    /\ UNCHANGED <<leader_term, mem_fully_repl, commit_log, god_log>>
    /\ UNCHANGED acceptor_vars
    /\ UNCHANGED global_term
    /\ UNCHANGED term_all_nodes

HandleVoteResp(n) ==
    \E resp \in vote_resp_msgs:
        /\ resp.type = "VoteResp"
        /\ resp.term = leader_term[n]
        /\ doHandleVoteResp(n, resp)

------------------------------------------------------------------

doHandleVoteReq(n, req, from_pos) ==
    LET
        final_pos ==
            IF from_pos > Len(acc_log[n])
                THEN from_pos
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

        resp_pos_set == {i \in DOMAIN acc_log[n]: i >= from_pos}
        normal_resp_set == {normal_resp(i): i \in resp_pos_set}
    IN
    /\ req.term >= acc_term[n]
    /\ final_resp \notin vote_resp_msgs

    /\ acc_term' = [acc_term EXCEPT ![n] = req.term]
    /\ vote_resp_msgs' = vote_resp_msgs \union normal_resp_set \union {final_resp}

    /\ UNCHANGED <<vote_req_msgs, acc_req_msgs, acc_resp_msgs>>
    /\ UNCHANGED acc_log
    /\ UNCHANGED leader_vars
    /\ UNCHANGED term_all_nodes

HandleVoteReq(n) ==
    \E req \in vote_req_msgs:
        /\ req.type = "VoteReq"
        /\ n \in term_all_nodes[req.term].all_nodes
        /\ doHandleVoteReq(n, req, term_all_nodes[req.term].from_pos)

------------------------------------------------------------------

candidate_vars == <<prepare_log, state, leader_term, global_term, remain_map>>

-----------------------

leader_commit_log_values(n) ==
    LET
        fully_repl == mem_fully_repl[n]
        acc_log_entries == SubSeq(acc_log[n], 1, fully_repl)
        acc_log_values == log_to_values(acc_log_entries)
    IN
        acc_log_values \o commit_log[n]

leader_commit_and_mem_log_values(n) ==
    leader_commit_log_values(n) \o log_to_values(mem_log[n])

-----------------------

num_entries_by_type(n, cmd_type) ==
    LET
        values == leader_commit_and_mem_log_values(n)
        cmd_set == {pos \in DOMAIN values: values[pos].type = cmd_type}
    IN
        Cardinality(cmd_set)

-----------------------

doLeaderNewCmd(n, v) ==
    /\ state[n] = "Leader"
    /\ num_entries_by_type(n, "Cmd") < max_cmd_len
    /\ append_mem_log(n, <<newCmd(v)>>)

    /\ UNCHANGED <<vote_req_msgs, vote_resp_msgs, acc_resp_msgs>>
    /\ UNCHANGED <<mem_fully_repl, members_info, commit_log, god_log>>
    /\ UNCHANGED candidate_vars
    /\ UNCHANGED acceptor_vars
    /\ UNCHANGED term_all_nodes

LeaderNewCmd(n) ==
    \E v \in Value: doLeaderNewCmd(n, v)

------------------------------------------------------------------

max_actual_member_len == (max_member_len - 1) * 2 + 1

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
    /\ num_entries_by_type(n, "Membership") < max_actual_member_len

    /\ append_mem_log(n, <<cmd>>)
    /\ members_info' = [members_info EXCEPT ![n] = new_members]

    /\ UNCHANGED <<vote_req_msgs, vote_resp_msgs, acc_resp_msgs>>
    /\ UNCHANGED <<mem_fully_repl, commit_log, god_log>>
    /\ UNCHANGED candidate_vars
    /\ UNCHANGED acceptor_vars
    /\ UNCHANGED term_all_nodes

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

        result == append_mem_log_result(n, <<cmd>>)
        new_mem_log == mem_log[n] \o result.mem_log
        move_result == move_from_mem_log_to_commit_log(new_mem_log, new_members)
    IN
    /\ state[n] = "Leader"
    /\ Len(members_info[n]) > 1
    /\ from_pos <= end_commit_pos(n)

    /\ members_info' = [members_info EXCEPT ![n] = new_members]
    /\ acc_req_msgs' = acc_req_msgs \union result.acc_req
    /\ mem_log' = [mem_log EXCEPT ![n] = move_result.mem_log]
    /\ append_commit_log(n, move_result.commit_log)

    /\ UNCHANGED <<vote_req_msgs, vote_resp_msgs, acc_resp_msgs>>
    /\ UNCHANGED <<mem_fully_repl>>
    /\ UNCHANGED candidate_vars
    /\ UNCHANGED acceptor_vars
    /\ UNCHANGED term_all_nodes

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

        already_committed ==
            /\ prev_entry # nil
            /\ prev_entry.term = infinity
    IN
    /\ req.term >= acc_term[n]
    /\ acc_resp \notin acc_resp_msgs

    /\ acc_resp_msgs' = acc_resp_msgs \union {acc_resp}
    /\ acc_term' = [acc_term EXCEPT ![n] = req.term]
    /\ IF already_committed
        THEN UNCHANGED acc_log
        ELSE acc_log' = [acc_log EXCEPT ![n] = PutSeqPos(@, pos, new_entry)]

    /\ UNCHANGED <<vote_req_msgs, vote_resp_msgs, acc_req_msgs>>
    /\ UNCHANGED leader_vars
    /\ UNCHANGED term_all_nodes

HandleAcceptReq(n) ==
    \E req \in acc_req_msgs:
        /\ req.type = "AcceptReq"
        /\ n \in term_all_nodes[req.term].all_nodes
        /\ doHandleAcceptReq(n, req)

------------------------------------------------------------------

doHandleAcceptResp(n, resp) ==
    LET
        pos == resp.pos
        y == resp.from_node
        index == pos - end_commit_pos(n)

        new_mem_log == [mem_log EXCEPT ![n][index].acceptors = @ \union {y}]
        result == move_from_mem_log_to_commit_log(new_mem_log[n], members_info[n])
    IN
    /\ state[n] \in {"Candidate", "Leader"}
    /\ pos > end_commit_pos(n)
    /\ y \notin mem_log[n][index].acceptors

    /\ mem_log' = [mem_log EXCEPT ![n] = result.mem_log]
    /\ append_commit_log(n, result.commit_log)

    /\ UNCHANGED msg_vars
    /\ UNCHANGED <<mem_fully_repl, members_info>>
    /\ UNCHANGED <<leader_term, global_term, state, prepare_log, remain_map>>
    /\ UNCHANGED acceptor_vars
    /\ UNCHANGED term_all_nodes

HandleAcceptResp(n) ==
    \E resp \in acc_resp_msgs:
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
    /\ UNCHANGED msg_vars
    /\ UNCHANGED term_all_nodes

ReplicateCommittedEntry(n) ==
    \E l \in Node:
        /\ leader_term[l] = acc_term[n]
        /\ state[l] \in {"Leader", "Candidate"}
        /\ doReplicateCommittedEntry(n, l)

------------------------------------------------------------------

doUpdateTermNodes(t, n) ==
    LET
        all_nodes == all_nodes_of_members({}, members_info[n])
        new_val == [
            all_nodes |-> all_nodes,
            from_pos |-> end_mem_pos(n) + 1
        ]
    IN
    /\ all_nodes # term_all_nodes[t].all_nodes
    /\ term_all_nodes' = [term_all_nodes EXCEPT ![t] = new_val]

    /\ UNCHANGED leader_vars
    /\ UNCHANGED acceptor_vars
    /\ UNCHANGED <<vote_req_msgs, vote_resp_msgs>>
    /\ UNCHANGED <<acc_req_msgs, acc_resp_msgs>>

UpdateTermNodes ==
    \E t \in Term, n \in Node:
        /\ leader_term[n] = t
        /\ state[n] # "Follower"
        /\ doUpdateTermNodes(t, n)

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
    /\ Len(god_log) >= max_cmd_len + max_actual_member_len
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
    \/ UpdateTermNodes
    \/ Terminated

Spec == Init /\ [][Next]_vars

------------------------------------------------------------------

LeaderTermInv ==
    \A n \in Node: leader_term[n] <= global_term

-----------------------

godLogStep ==
    LET
        new_len == Len(god_log')
        old_len == Len(god_log)
    IN
    /\ new_len > old_len
    /\ SubSeq(god_log', 1, old_len) = god_log

GodLogProperty ==
    [][godLogStep]_god_log

-----------------------

GodLogMatchCommitLog ==
    \A n \in Node:
        LET
            god_values == SubSeqSafe(god_log, 1, end_commit_pos(n))
            cond ==
                /\ end_commit_pos(n) <= Len(god_log)
                /\ leader_commit_log_values(n) = god_values
        IN
            state[n] \in {"Leader", "Candidate"} => cond

-----------------------

NonCandidateStateInv ==
    LET
        cond(n) ==
            /\ prepare_log[n] = <<>>
            /\ remain_map[n] = nil
    IN
    \A n \in Node:
        state[n] # "Candidate" => cond(n)

-----------------------

start_prepare_pos(n) ==
    end_mem_pos(n) + 1

leader_candidate_inv_cond(n) ==
    /\ mem_fully_repl[n] # nil
    /\ members_info[n] # nil

CandidateStateInv ==
    LET
        all_nodes_of(n) ==
            all_nodes_of_members({}, members_info[n])

        move_state(n) == [
            pos |-> start_prepare_pos(n),
            remain_map |-> remain_map[n],
            prepare_log |-> prepare_log[n],
            mem_log |-> <<>>,
            members_info |-> members_info[n]
        ]

        result_state(n) == move_from_prepare_log_to_mem_log(move_state(n))

        cond(n) ==
            /\ result_state(n).mem_log = <<>>
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

-----------------------

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

-----------------------

LeaderStateInv ==
    LET
        cond(n) ==
            /\ remain_map[n] = nil
            /\ prepare_log[n] = <<>>
            /\ leader_candidate_inv_cond(n)
    IN
    \A n \in Node:
        state[n] = "Leader" => cond(n)

-----------------------

InMemMembersInfoInv ==
    LET
        log_values(n) == leader_commit_and_mem_log_values(n)
        cond(n) == latest_members_info(nil, log_values(n)) = members_info[n]
    IN
    \A n \in Node:
        state[n] # "Follower" => cond(n)

-----------------------

accLogStepNode(n) ==
    LET
        before_pos == acceptor_fully_replicated_input_log(acc_log[n])
        after_pos == acceptor_fully_replicated_input_log(acc_log'[n])

        before_log == SubSeqSafe(acc_log[n], 1, before_pos)
        after_log == SubSeqSafe(acc_log'[n], 1, before_pos)
    IN
        /\ before_pos <= after_pos
        /\ before_log = after_log

accLogStep ==
    \A n \in Node: accLogStepNode(n)

AccLogProperty == [][accLogStep]_acc_log

-----------------------

MemLogFirstEntryInv ==
    LET
        pre_cond(n) ==
            /\ state[n] # "Follower"
            /\ mem_log[n] # <<>>

        entry(n) == mem_log[n][1]

        cond(n) ==
            ~is_quorum_of_members(entry(n).acceptors, members_info[n])
    IN
    \A n \in Node:
        pre_cond(n) => cond(n)

-----------------------

InversedInv ==
    Len(god_log) = 1

-----------------------

Perms == Permutations(Node) \union Permutations(Value)

-----------------------

\* TODO add property eventually state = Leader and mem_log = <<>>
\* TODO allow to disable a Node mid way

====

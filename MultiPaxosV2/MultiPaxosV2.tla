---- MODULE MultiPaxosV2 ----
EXTENDS PaxosUtil

CONSTANTS Node, Value, nop, max_log_len

VARIABLES
    global_term,
    state, leader_term, mem_fully_repl,
    remain_map, prepare_log, mem_log, commit_log,
    msgs,
    acc_term, acc_log,
    god_log

leader_vars == <<
    global_term,
    state, leader_term, mem_fully_repl,
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

LogPos == 0..4

InfLogPos == LogPos \union {infinity}

LeaderRemainMap == [Node -> Null(InfLogPos)]

-----------------------

NonEmpty(S) == S \ {}

MemberNodes == [
    nodes: NonEmpty(SUBSET Node),
    from: LogPos \ {0}
]

LogValue ==
    LET
        cmdValue == [
            type: {"Cmd"},
            val: Value \union {nop}
        ]

        memberValue == [
            type: {"Membership"},
            members: FiniteSeq(MemberNodes, 2)
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
    from_pos: LogPos
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

Msg ==
    UNION {VoteReqMsg, VoteRespMsg, AcceptReqMsg, AcceptRespMsg}

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
    /\ remain_map \in [Node -> Null(LeaderRemainMap)]
    /\ prepare_log \in [Node -> Seq(VoteLogEntry)]
    /\ mem_log \in [Node -> Seq(MemLogEntry)]
    /\ commit_log \in [Node -> Seq(LogValue)]

    /\ msgs \subseteq Msg

    /\ acc_term \in [Node -> Term]
    /\ acc_log \in [Node -> Seq(Null(LogEntry))]
    /\ god_log \in Seq(LogValue)

Init ==
    /\ global_term = 20

    /\ state = [n \in Node |-> "Follower"]
    /\ leader_term = [n \in Node |-> 20]
    /\ mem_fully_repl = [n \in Node |-> nil]
    /\ remain_map = [n \in Node |-> nil]
    /\ prepare_log = [n \in Node |-> <<>>]
    /\ mem_log = [n \in Node |-> <<>>]
    /\ commit_log = [n \in Node |-> <<>>]

    /\ msgs = {}

    /\ acc_term = [n \in Node |-> 20]
    /\ \E nodes \in NonEmpty(SUBSET Node):
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

StartElection(n) ==
    LET
        fully_replicated == acceptor_fully_replicated(n)

        start_pos == fully_replicated + 1

        vote_req == [
            type |-> "VoteReq",
            term |-> leader_term'[n],
            from_pos |-> start_pos
        ]

        new_remain_map == [y \in Node |-> start_pos]
    IN
    /\ state[n] = "Follower"
    /\ global_term' = global_term + 1
    /\ leader_term' = [leader_term EXCEPT ![n] = global_term']
    /\ mem_fully_repl' = [mem_fully_repl EXCEPT ![n] = fully_replicated]
    /\ state' = [state EXCEPT ![n] = "Candidate"]
    /\ msgs' = msgs \union {vote_req}
    /\ remain_map' = [remain_map EXCEPT ![n] = new_remain_map]
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

-----------------------

RECURSIVE start_non_proposed_entry_index(_, _, _, _)

start_non_proposed_entry_index(n, pos, input_remain_map, input_prepare_log) ==
    LET
        entry == input_prepare_log[1]
        acceptors == {y \in Node: log_pos_less(pos, input_remain_map[y])}
        is_proposed == acceptors \in QuorumOf(Node)
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

\* set all remain pos to be >= new_start_pos
set_remain_map_not_less_than(new_remain_map, new_start_pos) ==
    LET
        update_final_pos(old_pos) ==
            IF old_pos # infinity /\ old_pos < new_start_pos
                THEN new_start_pos
                ELSE old_pos
    IN
        [n \in DOMAIN new_remain_map |-> update_final_pos(new_remain_map[n])]

-----------------------

append_mem_log(n, values) ==
    LET
        new_entry_fn(v) == [
            value |-> v,
            acceptors |-> {},
            committed |-> FALSE
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

        \* check become leader
        inf_set == {x \in Node: new_remain_map[x] = infinity}
        switch_to_leader == inf_set \in QuorumOf(Node)
        when_become_leader ==
            /\ state' = [state EXCEPT ![n] = "Leader"]
            /\ remain_map' = [remain_map EXCEPT ![n] = nil]

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
        new_start_index == start_non_proposed_entry_index(
            n, end_mem_pos(n) + 1, new_remain_map, put_prepare_log
        )
        new_start_pos == end_mem_pos(n) + new_start_index

        new_prepare_log == RemoveSeqBefore(put_prepare_log, new_start_index)

        removed_prepare_log == SubSeq(put_prepare_log, 1, new_start_index - 1)
        mem_values == MapSeq(removed_prepare_log, LAMBDA entry: entry.value)

        final_remain_map == set_remain_map_not_less_than(
            new_remain_map, new_start_pos
        )

        when_normal ==
            /\ remain_map' = [remain_map EXCEPT ![n] = final_remain_map]
            /\ UNCHANGED state
    IN
    /\ state[n] = "Candidate"
    /\ remain_map[n][y] = resp.pos

    /\ prepare_log' = [prepare_log EXCEPT ![n] = new_prepare_log]
    /\ append_mem_log(n, mem_values)

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
        final_resp == [
            type |-> "VoteResp",
            term |-> req.term,
            from_node |-> n,
            more |-> FALSE,
            pos |-> Len(acc_log[n]) + 1,
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
        /\ doHandleVoteReq(n, req)

------------------------------------------------------------------

leader_commit_log_values(n) ==
    LET
        fully_repl == mem_fully_repl[n]
        acc_log_entries == SubSeq(acc_log[n], 1, fully_repl)
        acc_log_values == MapSeq(acc_log_entries, LAMBDA entry: entry.value)
    IN
        acc_log_values \o commit_log[n]

num_cmd_entries(n) ==
    LET
        mem_values == MapSeq(mem_log[n], LAMBDA entry: entry.value)
        values == leader_commit_log_values(n) \o mem_values
        cmd_set == {pos \in DOMAIN values: values[pos].type = "Cmd"}
    IN
        Cardinality(cmd_set)

doNewLeaderCmd(n, v) ==
    /\ state[n] = "Leader"
    /\ num_cmd_entries(n) < max_log_len
    /\ append_mem_log(n, <<newCmd(v)>>)
    /\ UNCHANGED <<state, leader_term, global_term, remain_map>>
    /\ UNCHANGED <<prepare_log, mem_fully_repl, commit_log, god_log>>
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
        /\ doHandleAcceptReq(n, req)

------------------------------------------------------------------

doHandleAcceptResp(n, resp) ==
    LET
        pos == resp.pos
        y == resp.from_node
        index == pos - end_commit_pos(n)

        new_mem_log == [mem_log EXCEPT ![n][index].acceptors = @ \union {y}]

        is_committed ==
            new_mem_log[n][index].acceptors \in QuorumOf(Node)

        set_committed == [new_mem_log EXCEPT ![n][index].committed = is_committed]
        new_log == set_committed[n]

        first_non_commit == FindFirstIndex(new_log, LAMBDA entry: ~entry.committed)

        new_committed == SubSeq(new_log, 1, first_non_commit - 1)
        new_committed_values == MapSeq(new_committed, LAMBDA entry: entry.value)
    IN
    /\ pos > end_commit_pos(n)
    /\ y \notin mem_log[n][index].acceptors
    /\ mem_log' = [set_committed EXCEPT ![n] = RemoveSeqBefore(@, first_non_commit)]
    /\ commit_log' = [commit_log EXCEPT ![n] = @ \o new_committed_values]

    /\ IF mem_fully_repl[n] + Len(commit_log'[n]) > Len(god_log)
        THEN god_log' = SubSeq(god_log, 1, mem_fully_repl[n]) \o commit_log'[n]
        ELSE UNCHANGED god_log

    /\ UNCHANGED msgs
    /\ UNCHANGED mem_fully_repl
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

CandidateStateInv ==
    LET
        non_proposed_index(n) ==
            start_non_proposed_entry_index(
                n, start_prepare_pos(n), remain_map[n], prepare_log[n]
            )

        cond(n) ==
            /\ non_proposed_index(n) = 1
            /\ mem_fully_repl[n] # nil
            /\ \A y \in Node:
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
    IN
    \A n \in Node:
        state[n] = "Follower" => cond(n)


LeaderStateInv ==
    LET
        cond(n) ==
            /\ remain_map[n] = nil
            /\ prepare_log[n] = <<>>
            /\ mem_fully_repl[n] # nil
    IN
    \A n \in Node:
        state[n] = "Leader" => cond(n)


InversedInv ==
    Len(god_log) = 0

====

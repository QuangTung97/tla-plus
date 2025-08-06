------ MODULE MultiPaxos ----
EXTENDS TLC, Naturals, FiniteSets, Sequences

CONSTANTS Node, nil

---------------------------------------------------------------

VARIABLES
    members, log, state, last_committed,
    global_last_term, last_propose_term, last_term,
    msgs

vars == <<
    members, log, state, last_committed,
    global_last_term, last_propose_term, last_term,
    msgs
>>

---------------------------------------------------------------

TermNum == 20..29
NullTerm == TermNum \union {nil}

LogPos == 0..20

LogEntry ==
    LET
        membership== [
            type: {"Member"},
            committed: BOOLEAN,
            term: NullTerm,
            nodes: SUBSET Node
        ]
    IN
        membership

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
            entry: LogEntry \union {nil},
            more: BOOLEAN
        ]
    IN
        UNION {request_vote, vote_response}

---------------------------------------------------------------

TypeOK ==
    /\ members \in [Node -> SUBSET Node]
    /\ log \in [Node -> Seq(LogEntry)]
    /\ last_committed \in [Node -> LogPos]
    /\ state \in [Node -> {"Follower", "Candidate", "Leader"}]
    /\ global_last_term \in TermNum
    /\ last_propose_term \in [Node -> TermNum]
    /\ last_term \in [Node -> TermNum]
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
    /\ init_members
    /\ state = [n \in Node |-> "Follower"]
    /\ global_last_term = 20
    /\ last_propose_term = [n \in Node |-> 20]
    /\ last_term = [n \in Node |-> 20]
    /\ msgs = {}

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
    IN
    /\ n \in members[n]
    /\ state[n] = "Follower"

    /\ global_last_term' = global_last_term + 1
    /\ state' = [state EXCEPT ![n] = "Candidate"]
    /\ last_propose_term' = [last_propose_term EXCEPT ![n] = global_last_term']

    /\ msgs' = msgs \union {req}

    /\ UNCHANGED <<log, last_committed>>
    /\ UNCHANGED last_term
    /\ UNCHANGED members


HandleRequestVote(n) ==
    \E req \in msgs:
        LET
            update_state ==
                IF req.from = n
                    THEN UNCHANGED state
                    ELSE UNCHANGED state \* TODO

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
        /\ last_term[n] < req.term
        /\ last_term' = [last_term EXCEPT ![n] = req.term]
        /\ update_state
        /\ msgs' = msgs \union {resp}

        /\ UNCHANGED last_propose_term
        /\ UNCHANGED global_last_term
        /\ UNCHANGED <<log, last_committed>>
        /\ UNCHANGED members


doHandleVoteResponse(n, resp) ==
    /\ resp.type = "VoteResponse"
    /\ state[n] = "Candidate"
    /\ last_propose_term[n] = resp.term

    /\ UNCHANGED last_propose_term
    /\ UNCHANGED last_term
    /\ UNCHANGED global_last_term
    /\ UNCHANGED <<log, last_committed>>
    /\ UNCHANGED members

HandleVoteResponse(n) ==
    \E resp \in msgs: doHandleVoteResponse(n, resp)


---------------------------------------------------------------

TerminateCond ==
    /\ TRUE

Terminated ==
    /\ UNCHANGED TerminateCond
    /\ UNCHANGED vars


Next ==
    \/ \E n \in Node:
        \/ StartElection(n)
        \/ HandleRequestVote(n)
        \/ HandleVoteResponse(n)
    \/ Terminated

Spec == Init /\ [][Next]_vars


====

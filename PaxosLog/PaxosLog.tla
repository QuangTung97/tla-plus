------ MODULE PaxosLog ----
EXTENDS TLC, Naturals, Sequences

CONSTANTS Node, nil, max_num_action

VARIABLES
    log, accept_log, computed_log,
    leader, current_term, curr_action

vars == <<
    log, accept_log, computed_log,
    leader, current_term, curr_action
>>

---------------------------------------------------------------

Term == 21..29

LogPos == 1..9

max_action == 30 + max_num_action
Action == 30..max_action
NullAction == Action \union {nil}

LogEntry == [
    pos: LogPos,
    term: Term,
    action: NullAction,
    commit: BOOLEAN
]

---------------------------------------------------------------

TypeOK ==
    /\ log \in Seq(LogEntry)
    /\ accept_log \in Seq(LogEntry)
    /\ computed_log \in Seq(LogEntry)

    /\ leader \in Node
    /\ current_term \in Term
    /\ curr_action \in Action

Init ==
    /\ log = <<>>
    /\ accept_log = <<>>
    /\ computed_log = <<>>

    /\ leader \in Node
    /\ current_term = 21
    /\ curr_action = 30

---------------------------------------------------------------

RECURSIVE computeAcceptLog(_)

computeAcceptLog(tmp_log) ==
    LET
        e == tmp_log[1]
    IN
    IF tmp_log = <<>> THEN
        <<>>
    ELSE IF e.commit THEN
        <<e>> \o computeAcceptLog(Tail(tmp_log))
    ELSE
        <<>>

globalAction ==
    /\ computed_log' = computeAcceptLog(log')

---------------------------------------------------------------

AddLog(n) ==
    LET
        pos == Len(log) + 1

        e == [
            pos |-> pos,
            term |-> current_term,
            action |-> curr_action',
            commit |-> FALSE
        ]
    IN
    /\ leader = n
    /\ curr_action < max_action

    /\ curr_action' = curr_action + 1
    /\ log' = Append(log, e)

    /\ UNCHANGED <<leader, current_term>>
    /\ UNCHANGED accept_log
    /\ globalAction

-----------------------------------

RECURSIVE highestCommitPos(_)

highestCommitPos(tmp_log) ==
    LET
        e == tmp_log[1]
    IN
    IF tmp_log = <<>> THEN
        0
    ELSE IF e.commit THEN
        1 + highestCommitPos(Tail(tmp_log))
    ELSE
        0


CommitEntry(n) ==
    \E pos \in DOMAIN log:
        LET
            e == log'[pos]
            commit_pos == highestCommitPos(log')
            next_pos == Len(accept_log) + 1

            append_to_accept ==
                accept_log' = accept_log \o SubSeq(log', next_pos, commit_pos)
        IN
        /\ leader = n
        /\ ~log[pos].commit

        /\ log' = [log EXCEPT ![pos].commit = TRUE]
        /\ IF commit_pos > Len(accept_log)
            THEN append_to_accept
            ELSE UNCHANGED accept_log

        /\ UNCHANGED <<leader, current_term>>
        /\ UNCHANGED curr_action
        /\ globalAction

---------------------------------------------------------------

TerminateCond ==
    /\ TRUE

Terminated ==
    /\ TerminateCond
    /\ UNCHANGED vars


Next ==
    \/ \E n \in Node:
        \/ AddLog(n)
        \/ CommitEntry(n)
    \/ Terminated

Spec == Init /\ [][Next]_vars

---------------------------------------------------------------

AcceptLogInv ==
    accept_log = computed_log

====

------ MODULE PaxosLog ----
EXTENDS TLC, Naturals, Sequences

CONSTANTS Node, nil, max_num_action

VARIABLES
    log, accept_log, computed_log,
    leader, state, current_term, curr_action

vars == <<
    log, accept_log, computed_log,
    leader, state, current_term, curr_action
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
NullEntry == LogEntry \union {nil}

---------------------------------------------------------------

TypeOK ==
    /\ log \in Seq(LogEntry)
    /\ accept_log \in Seq(NullEntry)
    /\ computed_log \in Seq(NullEntry)

    /\ leader \in Node
    /\ state \in {"Candidate", "Leader"}
    /\ current_term \in Term
    /\ curr_action \in Action

Init ==
    /\ log = <<>>
    /\ accept_log = <<>>
    /\ computed_log = <<>>

    /\ leader \in Node
    /\ state = "Leader"
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
        IF e.action = nil
            THEN <<nil>> \o computeAcceptLog(Tail(tmp_log))
            ELSE <<e>> \o computeAcceptLog(Tail(tmp_log))
    ELSE
        <<>>

globalAction ==
    /\ computed_log' = computeAcceptLog(log')

---------------------------------------------------------------

isLeader(n) ==
    /\ leader = n
    /\ state = "Leader"

incAction ==
    /\ curr_action < max_action
    /\ curr_action' = curr_action + 1

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
    /\ isLeader(n)
    /\ incAction
    /\ log' = Append(log, e)

    /\ UNCHANGED <<leader, state, current_term>>
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
        /\ isLeader(n)
        /\ ~log[pos].commit

        /\ log' = [log EXCEPT ![pos].commit = TRUE]
        /\ IF commit_pos > Len(accept_log)
            THEN append_to_accept
            ELSE UNCHANGED accept_log

        /\ UNCHANGED <<leader, state, current_term>>
        /\ UNCHANGED curr_action
        /\ globalAction

---------------------------------------------------------------

SwitchLeader(n) ==
    /\ leader # n
    /\ incAction

    /\ leader' = n
    /\ state' = "Candidate"
    /\ current_term' = current_term + 1

    /\ UNCHANGED <<log, accept_log>>
    /\ globalAction


isCandidate(n) ==
    /\ leader = n
    /\ state = "Candidate"

CandidateSetNull(n) ==
    LET
        update_entry(pos, old) ==
            IF old.commit THEN
                old
            ELSE
                [old EXCEPT !.term = current_term, !.action = nil]
    IN
    /\ isCandidate(n)

    /\ state' = "Leader"
    /\ log' = [pos \in DOMAIN log |-> update_entry(pos, log[pos])]

    /\ UNCHANGED accept_log
    /\ UNCHANGED curr_action
    /\ UNCHANGED <<leader, current_term>>
    /\ globalAction

---------------------------------------------------------------

TerminateCond ==
    /\ state = "Leader"
    /\ curr_action = max_action

Terminated ==
    /\ TerminateCond
    /\ UNCHANGED vars


Next ==
    \/ \E n \in Node:
        \/ AddLog(n)
        \/ CommitEntry(n)
        \/ SwitchLeader(n)
        \/ CandidateSetNull(n)
    \/ Terminated

Spec == Init /\ [][Next]_vars

---------------------------------------------------------------

LogPosInv ==
    \A pos \in DOMAIN log:
        pos = log[pos].pos


AcceptLogInv ==
    accept_log = computed_log


AcceptLogNotContainsNull ==
    \A pos \in DOMAIN accept_log:
        accept_log[pos] # nil => accept_log[pos].action # nil

====

------ MODULE PaxosLog ----
EXTENDS TLC, Naturals, Sequences

CONSTANTS Node, nil, max_num_action

VARIABLES
    log, prev,
    accept_log, accept_prev,
    computed_log,
    leader, state, current_term, curr_action

vars == <<
    log, prev,
    accept_log, accept_prev,
    computed_log,
    leader, state, current_term, curr_action
>>

---------------------------------------------------------------

Term == 21..29

LogPos == 1..9

max_action == 30 + max_num_action
Action == 30..max_action
NullAction == Action \union {nil}

PrevInfo == [
    pos: LogPos,
    term: Term
]
NullPrevInfo == PrevInfo \union {nil}

LogEntry == [
    pos: LogPos,
    term: Term,
    action: NullAction,
    prev: NullPrevInfo,
    commit: BOOLEAN
]
NullEntry == LogEntry \union {nil}

---------------------------------------------------------------

TypeOK ==
    /\ log \in Seq(LogEntry)
    /\ prev \in NullPrevInfo
    /\ accept_log \in Seq(NullEntry)
    /\ accept_prev \in NullPrevInfo
    /\ computed_log \in Seq(NullEntry)

    /\ leader \in Node
    /\ state \in {"Candidate", "Leader"}
    /\ current_term \in Term
    /\ curr_action \in Action

Init ==
    /\ log = <<>>
    /\ prev = nil
    /\ accept_log = <<>>
    /\ accept_prev = nil
    /\ computed_log = <<>>

    /\ leader \in Node
    /\ state = "Leader"
    /\ current_term = 21
    /\ curr_action = 30

---------------------------------------------------------------

RECURSIVE computeAcceptLog(_)

computeAcceptLog(obj) ==
    LET
        e == obj.log[1]

        normal_input == [
            log |-> Tail(obj.log),
            prev |-> [
                pos |-> e.pos,
                term |-> e.term
            ]
        ]
        normal_output == computeAcceptLog(normal_input)

        keep_input == [
            log |-> Tail(obj.log),
            prev |-> obj.prev
        ]
        keep_output == computeAcceptLog(keep_input)
    IN
    IF obj.log = <<>> THEN
        obj
    ELSE IF e.commit THEN
        IF e.action = nil \/ e.prev # obj.prev THEN
            [keep_output EXCEPT !.log = <<nil>> \o @]
        ELSE
            [normal_output EXCEPT !.log = <<e>> \o @]
    ELSE
        [obj EXCEPT !.log = <<>>]

globalAction ==
    /\ computed_log' = computeAcceptLog([
            log |-> log',
            prev |-> nil
        ]).log

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
            prev |-> prev,
            commit |-> FALSE
        ]

        new_prev == [
            pos |-> pos,
            term |-> current_term
        ]
    IN
    /\ isLeader(n)
    /\ incAction

    /\ log' = Append(log, e)
    /\ prev' = new_prev

    /\ UNCHANGED <<leader, state, current_term>>
    /\ UNCHANGED <<accept_log, accept_prev>>
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

RECURSIVE sanitizeAcceptEntries(_)

sanitizeAcceptEntries(obj) ==
    LET
        e == obj.log[1]

        next_prev == [
            pos |-> e.pos,
            term |-> e.term
        ]

        input == [
            log |-> Tail(obj.log),
            prev |-> next_prev
        ]
        next_obj == sanitizeAcceptEntries(input)

        keep_input == [
            log |-> Tail(obj.log),
            prev |-> obj.prev
        ]
        keep_obj == sanitizeAcceptEntries(keep_input)
    IN
    IF obj.log = <<>> THEN
        obj
    ELSE IF e.action = nil \/ e.prev # obj.prev THEN
        [keep_obj EXCEPT !.log = <<nil>> \o @]
    ELSE
        [next_obj EXCEPT !.log = <<e>> \o @]

CommitEntry(n) ==
    \E pos \in DOMAIN log:
        LET
            e == log'[pos]
            commit_pos == highestCommitPos(log')
            next_pos == Len(accept_log) + 1

            append_list == SubSeq(log', next_pos, commit_pos)
            input == [
                log |-> append_list,
                prev |-> accept_prev
            ]
            output == sanitizeAcceptEntries(input)

            append_to_accept ==
                /\ accept_log' = accept_log \o output.log
                /\ accept_prev' = output.prev

            do_nothing ==
                /\ UNCHANGED accept_log
                /\ UNCHANGED accept_prev
        IN
        /\ isLeader(n)
        /\ ~log[pos].commit

        /\ log' = [log EXCEPT ![pos].commit = TRUE]
        /\ IF commit_pos > Len(accept_log)
            THEN append_to_accept
            ELSE do_nothing

        /\ UNCHANGED prev
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
    /\ prev' = accept_prev

    /\ UNCHANGED <<log, accept_log, accept_prev>>
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

    /\ UNCHANGED prev
    /\ UNCHANGED <<accept_log, accept_prev>>
    /\ UNCHANGED curr_action
    /\ UNCHANGED <<leader, current_term>>
    /\ globalAction

---------------------------------------------------------------

TerminateCond ==
    /\ state = "Leader"
    /\ curr_action = max_action
    /\ Len(accept_log) = Len(log)

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

FairSpec == Spec /\ WF_vars(Next)

---------------------------------------------------------------

AlwaysTerminated == []<>TerminateCond


LogPosInv ==
    \A pos \in DOMAIN log:
        pos = log[pos].pos


AcceptLogInv ==
    accept_log = computed_log


AcceptLogMatchLog ==
    \A p \in DOMAIN accept_log:
        accept_log[p] # nil =>
            /\ accept_log[p] = log[p]
            /\ log[p].commit


AcceptLogNotContainsNull ==
    \A pos \in DOMAIN accept_log:
        accept_log[pos] # nil => accept_log[pos].action # nil


AcceptLogMustBeMonotonic ==
    \A p1, p2 \in DOMAIN accept_log:
        LET
            e1 == accept_log[p1]
            e2 == accept_log[p2]

            pre_cond ==
                /\ e1 # nil
                /\ e2 # nil
                /\ p1 < p2

            cond ==
                /\ e1.term <= e2.term
        IN
            pre_cond => cond


isAllNull(tmp_log) ==
    \A p \in DOMAIN tmp_log:
        tmp_log[p] = nil

subSeqWithEmpty(s, a, b) ==
    IF b = a - 1
        THEN <<>>
        ELSE SubSeq(s, a, b)

AcceptLogPrevInv ==
    \A p \in DOMAIN accept_log:
        LET
            e == accept_log[p]

            prev_pos ==
                IF e.prev = nil
                    THEN 0
                    ELSE e.prev.pos

            sub_seq == subSeqWithEmpty(accept_log, prev_pos + 1, p - 1)
        IN
            e # nil => isAllNull(sub_seq)

====

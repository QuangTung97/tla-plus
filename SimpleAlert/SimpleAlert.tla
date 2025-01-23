------ MODULE SimpleAlert ----
EXTENDS TLC, Naturals, Sequences

CONSTANTS Type, nil

VARIABLES state, status_list,
    pc, local_type, local_status, local_index,
    notify_list, num_update, num_disable

vars == <<state, status_list,
    pc, local_type, local_status, local_index,
    notify_list, num_update, num_disable>>

local_vars == <<pc, local_type, local_status, local_index>>

max_update == 5
max_send == 3
max_disable == 2
required_failed == 2

\* => Diameter = 41, Found = 670,875, Distinct = 221,392

NullType == Type \union {nil}

StateStatus == {"OK", "Failed"}

NullStatus == StateStatus \union {nil}

SendStatus == {"NoAction", "NeedSend", "Sending"}

State == [
    status: StateStatus,
    failed_count: 0..100,
    enabled: BOOLEAN,
    send_status: SendStatus,
    last_status: NullStatus,
    send_count: 0..100
]

Notify == [
    status: StateStatus,
    index: 1..100
]

TypeOK ==
    /\ state \in [Type -> State]
    /\ status_list \in [Type -> Seq(StateStatus)]
    /\ notify_list \in [Type -> Seq(Notify)]
    /\ pc \in {"Init", "SendNotify"}
    /\ local_type \in NullType
    /\ local_status \in NullStatus
    /\ local_index \in (1..100 \union {nil})
    /\ num_update \in 0..max_update
    /\ num_disable \in 0..max_disable

init_state == [
    status |-> "OK",
    failed_count |-> 0,
    enabled |-> TRUE,
    send_status |-> "NoAction",
    last_status |-> nil,
    send_count |-> 0
]

Init ==
    /\ state = [t \in Type |-> init_state]
    /\ status_list = [t \in Type |-> <<"OK">>]
    /\ notify_list = [t \in Type |-> <<>>]
    /\ pc = "Init"
    /\ local_type = nil
    /\ local_status = nil
    /\ local_index = nil
    /\ num_update = 0
    /\ num_disable = 0


doUpdateState(t, st) ==
    LET
        only_update_fail_count ==
            /\ st = "Failed"
            /\ state[t].failed_count + 1 < required_failed
        

        last_st == state[t].last_status

        update_to_need_alert ==
            \/ st = "Failed"
            \/

        \* to_need_send_cond ==
        \*     \/ st = "OK" /\ last_st = "Failed"
        \*     \/ st = "Failed"

        \* new_send_status ==
        \*     IF to_need_send_cond THEN
        \*         "NeedSend"
        \*     ELSE
        \*         "NoAction"

        \* old_status == state[t].send_status
        
        \* can_update ==
        \*     \/ old_status = "NoAction" /\ new_send_status # "NoAction"
        \*     \/ old_status \in {"NeedSend"} /\ new_send_status = "NoAction"
        
        \* new_fail_count ==
        \*     IF st = "OK" THEN
        \*         0
        \*     ELSE
        \*         state[t].failed_count + 1
    IN
        IF only_update_fail_count THEN
            state' = [state EXCEPT ![t].failed_count = @ + 1]
        ELSE IF can_update THEN
            state' = [state EXCEPT
                ![t].status = st,
                ![t].failed_count = new_fail_count,
                ![t].send_status = new_send_status
            ]
        ELSE
            state' = [state EXCEPT
                ![t].status = st,
                ![t].failed_count = 0
            ]

UpdateStatus(t) ==
    /\ num_update < max_update
    /\ num_update' = num_update + 1
    /\ \E st \in StateStatus:
        /\ doUpdateState(t, st)
        /\ status_list' = [status_list EXCEPT ![t] = Append(@, st)]
    /\ UNCHANGED local_vars
    /\ UNCHANGED <<notify_list>>
    /\ UNCHANGED num_disable


GetNeedAlert(t) ==
    LET
        new_send_status ==
            IF state[t].status = "OK"
                THEN "NoAction"
                ELSE "Sending"
    IN
    /\ pc = "Init"
    /\ state[t].enabled
    /\ state[t].send_status = "NeedSend"
    /\ pc' = "SendNotify"
    /\ state' = [state EXCEPT
            ![t].send_status = new_send_status,
            ![t].last_status = state[t].status,
            ![t].send_count = @ + 1
        ]
    /\ local_type' = t
    /\ local_status' = state[t].status
    /\ local_index' = Len(status_list[t])
    /\ UNCHANGED status_list
    /\ UNCHANGED notify_list
    /\ UNCHANGED num_update
    /\ UNCHANGED num_disable


RetrySendAlert(t) ==
    /\ state[t].send_status = "Sending"
    /\ state[t].enabled
    /\ state[t].send_count < max_send
    /\ state' = [state EXCEPT ![t].send_status = "NeedSend"]
    /\ UNCHANGED status_list
    /\ UNCHANGED local_vars
    /\ UNCHANGED notify_list
    /\ UNCHANGED num_update
    /\ UNCHANGED num_disable


SendNotify ==
    LET
        new_noti == [status |-> local_status, index |-> local_index]
    IN
    /\ pc = "SendNotify"
    /\ pc' = "Init"

    /\ notify_list' = [notify_list EXCEPT ![local_type] = Append(@, new_noti)]

    /\ local_type' = nil
    /\ local_status' = nil
    /\ local_index' = nil

    /\ UNCHANGED state
    /\ UNCHANGED status_list
    /\ UNCHANGED num_update
    /\ UNCHANGED num_disable


DisableState(t) ==
    /\ state[t].enabled
    /\ num_disable < max_disable
    /\ num_disable' = num_disable + 1
    /\ state' = [state EXCEPT ![t].enabled = FALSE]
    /\ UNCHANGED local_vars
    /\ UNCHANGED status_list
    /\ UNCHANGED notify_list
    /\ UNCHANGED num_update


EnableState(t) ==
    /\ ~state[t].enabled
    /\ state' = [state EXCEPT ![t].enabled = TRUE]
    /\ UNCHANGED local_vars
    /\ UNCHANGED status_list
    /\ UNCHANGED notify_list
    /\ UNCHANGED num_update
    /\ UNCHANGED num_disable



stopCond(t) ==
    /\ pc = "Init"
    /\ ~(ENABLED GetNeedAlert(t))
    /\ ~(ENABLED RetrySendAlert(t))

TerminateCond ==
    /\ \A t \in Type: stopCond(t)
    /\ num_update = max_update
    /\ num_disable = max_disable
    /\ \A t \in Type: state[t].enabled

Terminated ==
    /\ TerminateCond
    /\ UNCHANGED vars


Next ==
    \/ \E t \in Type:
        \/ UpdateStatus(t)
        \/ GetNeedAlert(t)
        \/ RetrySendAlert(t)
        \/ DisableState(t)
        \/ EnableState(t)
    \/ SendNotify
    \/ Terminated


Spec == Init /\ [][Next]_vars

FairSpec == Spec /\ WF_vars(Next)


AlwaysTerminate == <> TerminateCond


NotifyListMatchState ==
    \A t \in Type:
        LET
            list == notify_list[t]

            last_notify_is_failed ==
                /\ Len(list) > 0
                /\ list[Len(list)].status = "Failed"

            match_cond ==
                state[t].status = "Failed" <=> last_notify_is_failed

            is_enabled == state[t].enabled
        IN
            is_enabled /\ stopCond(t) => match_cond


NotSendDuplicateOK ==
    \A t \in Type:
        LET
            list == notify_list[t]

            pre_cond(idx) ==
                /\ idx > 1
                /\ list[idx].status = "OK"
        IN
            \A idx \in DOMAIN list:
                pre_cond(idx) => list[idx - 1].status # "OK"

FirstNotifyNotOK ==
    \A t \in Type:
        LET
            list == notify_list[t]
        IN
            \A idx \in DOMAIN list:
                idx = 1 => list[1].status = "Failed"


SendCountMaxNum ==
    \A t \in Type:
        state[t].send_count <= max_send


MustSendFullFailure ==
    \A t \in Type:
        LET
            pre_cond ==
                /\ stopCond(t)
                /\ state[t].enabled
                /\ state[t].status = "Failed"

            list == notify_list[t]

            end == Len(list)
            start == end - max_send + 1

            check_cond ==
                /\ Len(list) >= max_send
                /\ \A idx \in start..end: list[idx].status = "Failed"
        IN
            pre_cond => check_cond


MustNotSendWhenDisable ==
    \A t \in Type:
        ~state[t].enabled =>
            /\ ~(ENABLED GetNeedAlert(t))
            /\ ~(ENABLED RetrySendAlert(t))
            /\ ~(ENABLED DisableState(t))


StatusFailedRequiredFailCount ==
    \A t \in Type:
        state[t].status = "Failed" <=> state[t].failed_count = required_failed


ReverseInvStep ==
    \A t \in Type:
        \/ /\ state[t].status = "OK"
           /\ state'[t].status = "Failed"
        \/ state'[t].status = state[t].status


ReverseInv ==
    [][ReverseInvStep]_state

====

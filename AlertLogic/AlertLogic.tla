------ MODULE AlertLogic ----
EXTENDS TLC, Naturals, Sequences, FiniteSets

CONSTANTS Type, Key, nil, max_alerting

VARIABLES alert_enabled, need_alert,
    state, alerting, num_disable,
    send_info, status_list,
    notify_list, next_val,
    pc, local_type, local_status, local_index,
    num_alerting

vars == <<alert_enabled, need_alert,
    state, alerting, num_disable,
    send_info, status_list,
    notify_list, next_val, pc,
    local_type, local_status, local_index,
    num_alerting
>>

node_vars == <<pc, local_type, local_status, local_index>>

-----------------------------------------------------------------------------------

max_val == 33

max_send_count == 2

max_disable == 2

Value == 30..max_val

StateStatus == {"OK", "Failed"}

NullType == Type \union {nil}

NullStatus == StateStatus \union {nil}

State == [val: Value, status: StateStatus]

Notify == [type: Type, status: StateStatus, index: 1..100]

new_state == [val |-> 30, status |-> "OK"]

SendInfo == [
    enabled: BOOLEAN,
    count: 0..max_send_count,
    status: {"Sending", "Stopped", "Retrying"}
]

NullSendInfo == SendInfo \union {nil}

-----------------------------------------------------------------------------------

TypeOK ==
    /\ alert_enabled \in [Type -> BOOLEAN]
    /\ need_alert \subseteq Type
    /\ alerting \subseteq Type
    /\ num_disable \in 0..max_disable
    /\ send_info \in [Type -> NullSendInfo]
    /\ state \in [Type -> [Key -> State]]
    /\ notify_list \in Seq(Notify)
    /\ status_list \in [Type -> Seq(StateStatus)]
    /\ next_val \in Value
    /\ pc \in {"Init", "PushNotify", "ClearLocals"}
    /\ local_type \in NullType
    /\ local_status \in NullStatus
    /\ local_index \in (1..100 \union {nil})
    /\ num_alerting \in 0..Cardinality(Type)


Init ==
    /\ alert_enabled = [t \in Type |-> TRUE]
    /\ need_alert = {}
    /\ alerting = {}
    /\ num_disable = 0
    /\ send_info = [t \in Type |-> nil]
    /\ state = [t \in Type |-> [k \in Key |-> new_state]]
    /\ notify_list = <<>>
    /\ status_list = [t \in Type |-> <<>>]
    /\ next_val = 30
    /\ pc = "Init"
    /\ local_type = nil
    /\ local_status = nil
    /\ local_index = nil
    /\ num_alerting = 0

-----------------------------------------------------------------------------------

state_is_ok(t) ==
    \A k \in Key: state[t][k].status = "OK"

state_is_ok_new(t) ==
    \A k \in Key: state'[t][k].status = "OK"

UpdateKey(t, k) ==
    LET
        update_cond(status) ==
            /\ t \notin need_alert
            /\ IF status = "OK"
                THEN t \in alerting
                ELSE t \notin alerting

        update_changeset(status) ==
            IF update_cond(status) THEN
                /\ need_alert' = need_alert \union {t}
            ELSE
                /\ UNCHANGED need_alert

        new_st ==
            IF state_is_ok_new(t)
                THEN "OK"
                ELSE "Failed"

    IN
    /\ next_val < max_val
    /\ next_val' = next_val + 1
    /\ \E status \in {"OK", "Failed"}:
        /\ state' = [state EXCEPT
            ![t][k].val = next_val',
            ![t][k].status = status]
        /\ status_list' = [status_list EXCEPT ![t] = Append(@, new_st)]
        /\ update_changeset(status)
    /\ UNCHANGED <<alerting, num_alerting>>
    /\ UNCHANGED send_info
    /\ UNCHANGED notify_list
    /\ UNCHANGED node_vars
    /\ UNCHANGED <<alert_enabled, num_disable>>


GetChangedKey(t) ==
    LET
        new_status == IF state_is_ok(t) THEN "OK" ELSE "Failed"

        allow_send_fail ==
            /\ new_status = "Failed"
            /\ \/ send_info[t] = nil
               \/ send_info[t].status = "Retrying"
               \/ send_info[t].status = "Stopped"
        
        allow_send_success ==
            /\ new_status = "OK"
            /\ send_info[t] # nil
            /\ send_info[t].status # "Stopped"

        new_sending_info == [
            enabled |-> TRUE,
            count |-> 1,
            status |-> "Sending"
        ]

        set_info_sending ==
            IF send_info[t] = nil
                THEN send_info' = [send_info EXCEPT ![t] = new_sending_info]
                ELSE send_info' = [send_info EXCEPT
                        ![t].count = @ + 1,
                        ![t].status = "Sending"]
        
        new_stopped_info == [
            enabled |-> TRUE,
            count |-> 0,
            status |-> "Stopped"
        ]
    IN
    /\ pc = "Init"
    /\ t \in need_alert
    /\ alert_enabled[t]
    /\ need_alert' = need_alert \ {t} \* Remove from need_alert list

    /\ local_type' = t
    /\ local_status' = new_status
    /\ local_index' = Len(status_list[t])
    /\ IF allow_send_fail THEN
            /\ alerting' = alerting \union {t}
            /\ set_info_sending
            /\ pc' = "PushNotify"
        ELSE IF allow_send_success THEN
            /\ alerting' = alerting \ {t}
            /\ send_info' = [send_info EXCEPT ![t] = new_stopped_info]
            /\ pc' = "PushNotify"
        ELSE
            /\ UNCHANGED alerting
            /\ UNCHANGED send_info
            /\ pc' = "ClearLocals"
    /\ UNCHANGED num_alerting
    /\ UNCHANGED next_val
    /\ UNCHANGED notify_list
    /\ UNCHANGED status_list
    /\ UNCHANGED state
    /\ UNCHANGED <<alert_enabled, num_disable>>


doClearLocals ==
    /\ local_type' = nil
    /\ local_status' = nil
    /\ local_index' = nil

PushNotify ==
    LET
        noti_status == local_status

        new_noti == [
            type |-> local_type,
            status |-> noti_status,
            index |-> local_index
        ]
    IN
    /\ pc = "PushNotify"
    /\ pc' = "Init"
    /\ notify_list' = Append(notify_list, new_noti)
    /\ doClearLocals

    /\ UNCHANGED num_alerting
    /\ UNCHANGED alerting
    /\ UNCHANGED <<alert_enabled, num_disable>>
    /\ UNCHANGED send_info
    /\ UNCHANGED <<need_alert, state, next_val>>
    /\ UNCHANGED status_list


ClearLocals ==
    /\ pc = "ClearLocals"
    /\ pc' = "Init"
    /\ doClearLocals

    /\ UNCHANGED notify_list
    /\ UNCHANGED <<alerting, num_alerting>>
    /\ UNCHANGED <<alert_enabled, num_disable>>
    /\ UNCHANGED send_info
    /\ UNCHANGED <<need_alert, state, next_val>>
    /\ UNCHANGED status_list


can_retry(t) ==
    send_info[t].status = "Sending"

RetrySendAlert(t) ==
    /\ send_info[t] # nil
    /\ send_info[t].status = "Sending"
    /\ send_info[t].enabled
    /\ send_info[t].count < max_send_count

    /\ need_alert' = need_alert \union {t}
    /\ send_info' = [send_info EXCEPT ![t].status = "Retrying"]

    /\ UNCHANGED num_alerting
    /\ UNCHANGED alerting
    /\ UNCHANGED notify_list
    /\ UNCHANGED status_list
    /\ UNCHANGED <<next_val, state>>
    /\ UNCHANGED node_vars
    /\ UNCHANGED <<alert_enabled, num_disable>>


DisableAlert(t) ==
    /\ alert_enabled[t]
    /\ num_disable < max_disable
    /\ num_disable' = num_disable + 1
    /\ alert_enabled' = [alert_enabled EXCEPT ![t] = FALSE]
    /\ IF send_info[t] # nil
        THEN send_info' = [send_info EXCEPT ![t].enabled = FALSE]
        ELSE UNCHANGED send_info
    /\ UNCHANGED num_alerting \* TODO
    /\ UNCHANGED state
    /\ UNCHANGED <<need_alert, alerting>>
    /\ UNCHANGED next_val
    /\ UNCHANGED notify_list
    /\ UNCHANGED status_list
    /\ UNCHANGED node_vars


EnableAlert(t) ==
    /\ ~alert_enabled[t]
    /\ alert_enabled' = [alert_enabled EXCEPT ![t] = TRUE]
    /\ IF send_info[t] # nil
        THEN send_info' = [send_info EXCEPT ![t].enabled = TRUE]
        ELSE UNCHANGED send_info
    /\ UNCHANGED num_alerting \* TODO
    /\ UNCHANGED num_disable
    /\ UNCHANGED state
    /\ UNCHANGED <<need_alert, alerting>>
    /\ UNCHANGED next_val
    /\ UNCHANGED notify_list
    /\ UNCHANGED status_list
    /\ UNCHANGED node_vars

-----------------------------------------------------------------------------------

notifyStopCond ==
    /\ pc = "Init"
    /\ need_alert = {}

TerminateCond ==
    /\ notifyStopCond
    /\ next_val = max_val
    /\ \A t \in Type: ~state_is_ok(t) => send_info[t].count = max_send_count

Terminated ==
    /\ TerminateCond
    /\ UNCHANGED vars


Next ==
    \/ \E t \in Type, k \in Key:
        \/ UpdateKey(t, k)

    \/ \E t \in Type:
        \/ RetrySendAlert(t)
        \/ GetChangedKey(t)
        \/ DisableAlert(t)
        \/ EnableAlert(t)
    \/ PushNotify
    \/ ClearLocals
    \/ Terminated


Spec == Init /\ [][Next]_vars

FairSpec == Spec /\ WF_vars(Next)

-----------------------------------------------------------------------------------

AlwaysTerminate == <> TerminateCond


maxOfSet(set) ==
    CHOOSE x \in set: \A y \in set: y <= x


notify_by_type(t) ==
    {i \in DOMAIN notify_list: notify_list[i].type = t}

last_noti(t) ==
    notify_list[maxOfSet(notify_by_type(t))]


NotifyListReflectState ==
    LET
        match_cond(t) ==
            notify_by_type(t) # {} =>
                \/ last_noti(t).status = "Failed" /\ ~state_is_ok(t)
                \/ last_noti(t).status = "OK" /\ state_is_ok(t)
        
        must_pushed(t) == \* state failed => must push to the notify list
            ~state_is_ok(t) => notify_by_type(t) # {}
                
        match_notify_list ==
            \A t \in Type:
                alert_enabled[t] =>
                    /\ match_cond(t)
                    /\ must_pushed(t)
    IN
        notifyStopCond => match_notify_list


AlertingMatchState ==
    LET
        alert_cond(t) ==
            /\ notify_by_type(t) # {}
            /\ last_noti(t).status = "Failed"

        match_cond ==
            \A t \in Type:
                t \in alerting <=> alert_cond(t)
    IN
        notifyStopCond => match_cond


SendCountZeroForOK ==
    LET
        is_non_zero(t) ==
            /\ send_info[t] # nil
            /\ send_info[t].count > 0
    IN
        \A t \in Type:
            (t \in alerting <=> is_non_zero(t))


SendCountLimit ==
    \A t \in Type: send_info[t] # nil =>
        send_info[t].count <= max_send_count


SendStatusActiveWhenAlert ==
    LET
        is_active(t) ==
            /\ send_info[t] # nil
            /\ send_info[t].status \in {"Sending", "Retrying"}
    IN
        \A t \in Type: t \in alerting <=> is_active(t)


AlwaysEnabledGetOrRetry ==
    \A t \in Type:
        ~state_is_ok(t) /\ alert_enabled[t] =>
            \/ pc = "Init" => ENABLED GetChangedKey(t)
            \/ send_info[t].count < max_send_count =>
                    ENABLED RetrySendAlert(t)


CheckEnabledPushNotify ==
    pc = "PushNotify" => ENABLED PushNotify


NotRetryWhenDisabled ==
    \A t \in Type:
        ~alert_enabled[t] => ~(ENABLED RetrySendAlert(t))


AlertEnabledMatchSendInfo ==
    \A t \in Type: send_info[t] # nil =>
        alert_enabled[t] <=> send_info[t].enabled


CanRetryMatchRunning ==
    LET
        cond(t) ==
            /\ send_info[t].status = "Sending"
    IN
    \A t \in Type: send_info[t] # nil =>
        (can_retry(t) => cond(t))


checkStatusList(t, list) ==
    \A idx \in DOMAIN list:
        LET
            e == list[idx]

            prev ==
                IF idx > 1
                    THEN list[idx - 1]
                    ELSE nil

            pre_cond ==
                status_list[t][e.index] = "OK"

            cond ==
                /\ prev # nil
                /\ status_list[t][prev.index] = "Failed"
        IN
            pre_cond => cond

StatusListSuccessMustFollowFail ==
    \A t \in Type:
        LET
            select_list(x) == x.type = t

            list == SelectSeq(notify_list, select_list)
        IN
            checkStatusList(t, list)


PCInitInv ==
    pc = "Init" =>
        /\ local_type = nil
        /\ local_status = nil
        /\ local_index = nil


NeedAlertEmptyWhenTerminate ==
    notifyStopCond =>
        /\ need_alert = {}
        /\ \A t \in Type:
            state_is_ok(t) <=> t \notin alerting


LimitNumAlerting ==
    Cardinality(alerting) <= max_alerting


Sym == Permutations(Type) \union Permutations(Key)

====

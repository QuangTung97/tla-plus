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
    status: {"None", "Sending", "Stopped", "Retrying"},
    paused: BOOLEAN
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


is_paused(t) ==
    /\ send_info[t] # nil
    /\ send_info[t].paused

GetChangedKey(t) ==
    LET
        new_status == IF state_is_ok(t) THEN "OK" ELSE "Failed"

        new_num_alerting ==
            IF t \notin alerting
                THEN num_alerting + 1
                ELSE num_alerting

        allow_send_fail ==
            /\ new_status = "Failed"
            /\ \/ send_info[t] = nil
               \/ /\ send_info[t].status \in {"None", "Retrying", "Stopped"}
                  /\ ~send_info[t].paused

        do_send_fail ==
            /\ allow_send_fail
            /\ new_num_alerting <= max_alerting

        pause_sending == allow_send_fail

        allow_send_success ==
            /\ new_status = "OK"
            /\ send_info[t] # nil
            /\ send_info[t].status \notin {"None", "Stopped"}

        new_sending_info == [
            enabled |-> TRUE,
            count |-> 1,
            status |-> "Sending",
            paused |-> FALSE
        ]

        set_info_sending ==
            IF send_info[t] = nil
                THEN send_info' = [send_info EXCEPT ![t] = new_sending_info]
                ELSE send_info' = [send_info EXCEPT
                        ![t].count = @ + 1,
                        ![t].status = "Sending"]

        new_paused_info == [
            enabled |-> TRUE,
            count |-> 0,
            status |-> "None",
            paused |-> TRUE
        ]

        new_stopped_info == [
            enabled |-> TRUE,
            count |-> 0,
            status |-> "Stopped",
            paused |-> FALSE
        ]
    IN
    /\ pc = "Init"
    /\ t \in need_alert
    /\ alert_enabled[t]
    /\ need_alert' = need_alert \ {t} \* Remove from need_alert list

    /\ local_type' = t
    /\ local_status' = new_status
    /\ local_index' = Len(status_list[t])
    /\ IF do_send_fail THEN
            /\ alerting' = alerting \union {t}
            /\ num_alerting' = new_num_alerting
            /\ set_info_sending
            /\ pc' = "PushNotify"
        ELSE IF pause_sending THEN
            /\ UNCHANGED alerting
            /\ UNCHANGED num_alerting
            /\ send_info' = [send_info EXCEPT ![t] = new_paused_info]
            /\ pc' = "ClearLocals"
        ELSE IF allow_send_success THEN
            /\ alerting' = alerting \ {t}
            /\ IF send_info[t].paused
                THEN UNCHANGED num_alerting
                ELSE num_alerting' = num_alerting - 1
            /\ send_info' = [send_info EXCEPT ![t] = new_stopped_info]
            /\ pc' = "PushNotify"
        ELSE
            /\ UNCHANGED alerting
            /\ UNCHANGED num_alerting
            /\ UNCHANGED send_info
            /\ pc' = "ClearLocals"
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


RetrySendAlert(t) ==
    /\ send_info[t] # nil
    /\ send_info[t].enabled \* TODO check index
    /\ ~send_info[t].paused
    /\ send_info[t].status = "Sending"
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
    LET
        dec_cond ==
            /\ t \in alerting
            /\ ~is_paused(t)
    IN
    /\ alert_enabled[t]
    /\ num_disable < max_disable
    /\ num_disable' = num_disable + 1
    /\ alert_enabled' = [alert_enabled EXCEPT ![t] = FALSE]
    /\ IF send_info[t] # nil
        THEN send_info' = [send_info EXCEPT ![t].enabled = FALSE]
        ELSE UNCHANGED send_info
    /\ IF dec_cond
        THEN num_alerting' = num_alerting - 1
        ELSE UNCHANGED num_alerting
    /\ UNCHANGED state
    /\ UNCHANGED <<need_alert, alerting>>
    /\ UNCHANGED next_val
    /\ UNCHANGED notify_list
    /\ UNCHANGED status_list
    /\ UNCHANGED node_vars


EnableAlert(t) ==
    LET
        updated == [send_info EXCEPT ![t].enabled = TRUE]

        new_num_alerting ==
            IF t \in alerting
                THEN num_alerting + 1
                ELSE num_alerting

        need_pause_info ==
            \/ new_num_alerting > max_alerting
            \/ send_info[t].paused

        do_update ==
            IF send_info[t] # nil THEN
                IF need_pause_info
                    THEN
                        /\ send_info' = [updated EXCEPT ![t].paused = TRUE]
                        /\ UNCHANGED num_alerting
                    ELSE
                        /\ send_info' = updated
                        /\ num_alerting' = new_num_alerting
            ELSE
                /\ UNCHANGED send_info
                /\ UNCHANGED num_alerting
    IN
    /\ ~alert_enabled[t]
    /\ alert_enabled' = [alert_enabled EXCEPT ![t] = TRUE]
    /\ do_update
    /\ UNCHANGED num_disable
    /\ UNCHANGED state
    /\ UNCHANGED <<need_alert, alerting>>
    /\ UNCHANGED next_val
    /\ UNCHANGED notify_list
    /\ UNCHANGED status_list
    /\ UNCHANGED node_vars


UnpauseInfo(t) ==
    /\ num_alerting < max_alerting
    /\ send_info[t] # nil
    /\ send_info[t].paused \* TODO check index
    /\ send_info[t].enabled

    /\ need_alert' = need_alert \union {t}
    /\ send_info' = [send_info EXCEPT ![t].paused = FALSE]
    /\ IF t \in alerting
        THEN num_alerting' = num_alerting + 1
        ELSE UNCHANGED num_alerting
    /\ UNCHANGED <<alerting>>

    /\ UNCHANGED state
    /\ UNCHANGED <<alert_enabled>>
    /\ UNCHANGED num_disable
    /\ UNCHANGED next_val
    /\ UNCHANGED notify_list
    /\ UNCHANGED status_list
    /\ UNCHANGED node_vars

-----------------------------------------------------------------------------------

notifyStopCond ==
    /\ pc = "Init"
    /\ need_alert = {}

TerminateCond ==
    LET
        max_count_pre_cond(t) ==
            /\ ~state_is_ok(t)
            /\ ~is_paused(t)
    IN
    /\ notifyStopCond
    /\ next_val = max_val
    /\ \A t \in Type: max_count_pre_cond(t) => send_info[t].count = max_send_count
    /\ \A t \in Type: alert_enabled[t]

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
        \/ UnpauseInfo(t)
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

        pre_cond(t) ==
            /\ alert_enabled[t]
            /\ ~is_paused(t)

        match_notify_list ==
            \A t \in Type:
                pre_cond(t) =>
                    /\ match_cond(t)
                    /\ must_pushed(t)
    IN
        notifyStopCond => match_notify_list


AlertingMatchState ==
    LET
        alert_cond(t) ==
            /\ notify_by_type(t) # {}
            /\ last_noti(t).status = "Failed"

        cond(t) ==
            t \in alerting <=> alert_cond(t)

        match_cond ==
            \A t \in Type: cond(t)
    IN
        notifyStopCond => match_cond


SendCountZeroForOK ==
    LET
        is_non_zero(t) ==
            /\ send_info[t] # nil
            /\ send_info[t].count > 0

        cond(t) ==
            t \in alerting <=> is_non_zero(t)
    IN
        \A t \in Type: cond(t)


SendCountLimit ==
    \A t \in Type: send_info[t] # nil =>
        send_info[t].count <= max_send_count


SendStatusActiveWhenAlert ==
    LET
        is_active(t) ==
            /\ send_info[t] # nil
            /\ send_info[t].status \in {"Sending", "Retrying"}

        cond(t) ==
            t \in alerting <=> is_active(t)
    IN
        \A t \in Type: cond(t)


AlwaysEnabledGetOrRetry ==
    LET
        pre_cond(t) ==
            /\ ~state_is_ok(t)
            /\ alert_enabled[t]
    IN
    \A t \in Type:
        pre_cond(t) =>
            \/ pc = "Init" => ENABLED GetChangedKey(t)
            \/ send_info[t].count < max_send_count => ENABLED RetrySendAlert(t)
            \/ send_info[t].paused


CheckEnabledPushNotify ==
    pc = "PushNotify" => ENABLED PushNotify


NotRetryWhenDisabled ==
    \A t \in Type:
        ~alert_enabled[t] => ~(ENABLED RetrySendAlert(t))


AlertEnabledMatchSendInfo ==
    \A t \in Type: send_info[t] # nil =>
        alert_enabled[t] <=> send_info[t].enabled


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
    LET
        cond(t) ==
            state_is_ok(t) <=> t \notin alerting
    IN
    notifyStopCond =>
        /\ need_alert = {}
        /\ \A t \in Type: ~is_paused(t) => cond(t)


enable_alerting_set ==
    {t \in alerting: alert_enabled[t] /\ ~is_paused(t)}

NumAlertingInv ==
    Cardinality(enable_alerting_set) = num_alerting

LimitNumAlerting ==
    Cardinality(enable_alerting_set) <= max_alerting


PauseListIsEmptyWhenNotReachMaxAlerting ==
    LET
        can_unpause(t) == ENABLED UnpauseInfo(t)

        pre_cond ==
            /\ Cardinality(enable_alerting_set) < max_alerting

        inv_cond ==
            \A t \in Type: alert_enabled[t] =>
                \/ ~is_paused(t)
                \/ can_unpause(t)
    IN
        pre_cond => inv_cond


NeverPauseWhenNoLimit ==
    LET
        no_limit == max_alerting >= Cardinality(Type)

        no_pause ==
            \A t \in Type:
                send_info[t] # nil => ~send_info[t].paused
    IN
        no_limit => no_pause


Sym == Permutations(Type) \union Permutations(Key)

====

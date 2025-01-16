------ MODULE AlertLogic ----
EXTENDS TLC, Naturals, Sequences

CONSTANTS Type, Key, nil

VARIABLES alert_enabled, need_alert,
    state, alerting, num_disable,
    send_info,
    notify_list, next_val, pc, local_type, local_status

vars == <<alert_enabled, need_alert,
    state, alerting, num_disable,
    send_info,
    notify_list, next_val, pc, local_type, local_status>>

node_vars == <<pc, local_type, local_status>>


max_val == 33 \* TODO prev = 34

max_send_count == 2 \* TODO prev = 3

max_disable == 2

Value == 30..max_val

StateStatus == {"OK", "Failed"}

NullType == Type \union {nil}

NullStatus == StateStatus \union {nil}

State == [val: Value, status: StateStatus]

Notify == [type: Type, status: StateStatus]

new_state == [val |-> 30, status |-> "OK"]

SendInfo == [
    enabled: BOOLEAN,
    count: 0..max_send_count,
    status: {"Active", "Disabled"},
    last_status: NullStatus
]

NullSendInfo == SendInfo \union {nil}


TypeOK ==
    /\ alert_enabled \in [Type -> BOOLEAN]
    /\ need_alert \subseteq Type
    /\ alerting \subseteq Type
    /\ num_disable \in 0..max_disable
    /\ send_info \in [Type -> NullSendInfo]
    /\ state \in [Type -> [Key -> State]]
    /\ notify_list \in Seq(Notify)
    /\ next_val \in Value
    /\ pc \in {"Init", "PushNotify"}
    /\ local_type \in NullType
    /\ local_status \in NullStatus


Init ==
    /\ alert_enabled = [t \in Type |-> TRUE]
    /\ need_alert = {}
    /\ alerting = {}
    /\ num_disable = 0
    /\ send_info = [t \in Type |-> nil]
    /\ state = [t \in Type |-> [k \in Key |-> new_state]]
    /\ notify_list = <<>>
    /\ next_val = 30
    /\ pc = "Init"
    /\ local_type = nil
    /\ local_status = nil


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
    IN
    /\ next_val < max_val
    /\ next_val' = next_val + 1
    /\ \E status \in {"OK", "Failed"}:
        /\ state' = [state EXCEPT
            ![t][k].val = next_val',
            ![t][k].status = status]
        /\ update_changeset(status)
    /\ UNCHANGED alerting
    /\ UNCHANGED send_info
    /\ UNCHANGED notify_list
    /\ UNCHANGED node_vars
    /\ UNCHANGED <<alert_enabled, num_disable>>


state_is_ok(t) ==
    \A k \in Key: state[t][k].status = "OK"



GetChangedKey(t) ==
    LET
        not_allow_set_active ==
            /\ send_info[t] # nil
            /\ local_status' = send_info[t].last_status
        
        allow_set_active == ~not_allow_set_active

        new_failed == [
            enabled |-> TRUE,
            count |-> 1,
            status |-> "Active",
            last_status |-> nil
        ]

        set_active ==
            IF send_info[t] = nil
                THEN send_info' = [send_info EXCEPT ![t] = new_failed]
                ELSE send_info' = [send_info EXCEPT
                        ![t].count = @ + 1,
                        ![t].status = "Active",
                        ![t].last_status = local_status']
        
        new_info_disabled == [
            enabled |-> TRUE,
            count |-> 0,
            status |-> "Disabled",
            last_status |-> nil
        ]
    IN
    /\ pc = "Init"
    /\ t \in need_alert
    /\ alert_enabled[t]
    /\ need_alert' = need_alert \ {t} \* Remove from need_alert list

    /\ local_type' = t
    /\ local_status' = IF state_is_ok(t) THEN "OK" ELSE "Failed"
    /\ pc' = "PushNotify"
    /\ IF local_status' = "Failed" THEN
            IF allow_set_active THEN
                /\ alerting' = alerting \union {t}
                /\ set_active
            ELSE
                /\ UNCHANGED alerting
                /\ UNCHANGED send_info
        ELSE
            /\ alerting' = alerting \ {t}
            /\ send_info' = [send_info EXCEPT ![t] = new_info_disabled]
    /\ UNCHANGED next_val
    /\ UNCHANGED notify_list
    /\ UNCHANGED state
    /\ UNCHANGED <<alert_enabled, num_disable>>


PushNotify ==
    LET
        noti_status == local_status

        new_noti == [type |-> local_type, status |-> noti_status]
    IN
    /\ pc = "PushNotify"
    /\ pc' = "Init"
    /\ notify_list' = Append(notify_list, new_noti)

    /\ local_type' = nil \* clear local
    /\ local_status' = nil \* clear local

    /\ UNCHANGED alerting
    /\ UNCHANGED <<alert_enabled, num_disable>>
    /\ UNCHANGED send_info
    /\ UNCHANGED <<need_alert, state, next_val>>


RetrySendAlert(t) ==
    /\ send_info[t] # nil
    /\ send_info[t].status = "Active"
    /\ send_info[t].enabled
    /\ t \notin need_alert
    /\ send_info[t].count < max_send_count

    /\ need_alert' = need_alert \union {t}
    /\ send_info' = [send_info EXCEPT ![t].last_status = nil]

    /\ UNCHANGED alerting
    /\ UNCHANGED notify_list
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
    /\ UNCHANGED state
    /\ UNCHANGED <<need_alert, alerting>>
    /\ UNCHANGED next_val
    /\ UNCHANGED notify_list
    /\ UNCHANGED node_vars


EnableAlert(t) ==
    /\ ~alert_enabled[t]
    /\ alert_enabled' = [alert_enabled EXCEPT ![t] = TRUE]
    /\ IF send_info[t] # nil
        THEN send_info' = [send_info EXCEPT ![t].enabled = TRUE]
        ELSE UNCHANGED send_info
    /\ UNCHANGED num_disable
    /\ UNCHANGED state
    /\ UNCHANGED <<need_alert, alerting>>
    /\ UNCHANGED next_val
    /\ UNCHANGED notify_list
    /\ UNCHANGED node_vars


TerminateCond ==
    /\ next_val = max_val
    /\ pc = "Init"
    /\ need_alert = {}

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
    \/ Terminated


Spec == Init /\ [][Next]_vars

FairSpec == Spec /\ WF_vars(Next)

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
        TerminateCond => match_notify_list


AlertingMatchState ==
    LET
        alert_cond(t) ==
            /\ notify_by_type(t) # {}
            /\ last_noti(t).status = "Failed"

        match_cond ==
            \A t \in Type:
                t \in alerting <=> alert_cond(t)
    IN
        TerminateCond => match_cond


SendCountZeroForOK ==
    \A t \in Type: send_info[t] # nil =>
        (t \notin alerting <=> send_info[t].count = 0)


SendCountLimit ==
    \A t \in Type: send_info[t] # nil =>
        send_info[t].count <= max_send_count


SendStatusActiveWhenAlert ==
    \A t \in Type: send_info[t] # nil =>
        t \in alerting <=> send_info[t].status = "Active"


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


Sym == Permutations(Type) \union Permutations(Key)

====

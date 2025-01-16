------ MODULE AlertLogic ----
EXTENDS TLC, Naturals, Sequences

CONSTANTS Type, Key, nil

VARIABLES version, alert_enabled, need_alert,
    state, alerting,
    send_info,
    notify_list, next_val, pc, local_type, local_status

vars == <<version, alert_enabled, need_alert,
    state, alerting,
    send_info,
    notify_list, next_val, pc, local_type, local_status>>

node_vars == <<pc, local_type, local_status>>


max_val == 35

max_send_count == 1

Version == 20..30

Value == 30..40

StateStatus == {"OK", "Failed"}

NullType == Type \union {nil}

NullStatus == StateStatus \union {nil}

State == [val: Value, status: StateStatus]

Notify == [type: Type, status: StateStatus]

new_state == [val |-> 30, status |-> "OK"]

SendInfo == [count: Nat, status: {"Active", "Disabled"}, last_status: NullStatus]


TypeOK ==
    /\ version \in Version
    /\ alert_enabled \in [Type -> BOOLEAN]
    /\ need_alert \subseteq Type
    /\ alerting \subseteq Type
    /\ send_info \in [Type -> SendInfo]
    /\ state \in [Type -> [Key -> State]]
    /\ notify_list \in Seq(Notify)
    /\ next_val \in Value
    /\ pc \in {"Init", "PushNotify"}
    /\ local_type \in NullType
    /\ local_status \in NullStatus

init_send_info == [count |-> 0, status |-> "Disabled", last_status |-> nil]

Init ==
    /\ version = 20
    /\ alert_enabled = [t \in Type |-> TRUE]
    /\ need_alert = {}
    /\ alerting = {}
    /\ send_info = [t \in Type |-> init_send_info]
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
                /\ version' = version + 1
            ELSE
                /\ UNCHANGED need_alert
                /\ UNCHANGED version
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
    /\ UNCHANGED alert_enabled


state_is_ok(t) ==
    \A k \in Key: state[t][k].status = "OK"

GetChangedKey(t) ==
    /\ pc = "Init"
    /\ t \in need_alert
    /\ need_alert' = need_alert \ {t}

    /\ local_type' = t
    /\ local_status' = IF state_is_ok(t) THEN "OK" ELSE "Failed"
    /\ pc' = "PushNotify"
    /\ IF local_status' = "Failed" THEN
        IF local_status' # send_info[t].last_status
            THEN
                /\ alerting' = alerting \union {t}
                /\ send_info' = [send_info EXCEPT
                        ![t].count = @ + 1,
                        ![t].status = "Active",
                        ![t].last_status = local_status']
            ELSE
                /\ UNCHANGED alerting
                /\ UNCHANGED send_info
        ELSE
            /\ alerting' = alerting \ {t}
            /\ send_info' = [send_info EXCEPT
                    ![t].count = 0,
                    ![t].status = "Disabled",
                    ![t].last_status = local_status']

    /\ UNCHANGED next_val
    /\ UNCHANGED notify_list
    /\ UNCHANGED <<state, version>>
    /\ UNCHANGED alert_enabled


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
    /\ UNCHANGED alert_enabled
    /\ UNCHANGED send_info
    /\ UNCHANGED <<need_alert, version, state, next_val>>


retry_update_cond(t) ==
    /\ t \notin need_alert
    /\ send_info[t].count < max_send_count

RetrySendAlert(t) ==
    /\ send_info[t].status = "Active"
    /\ IF retry_update_cond(t)
        THEN need_alert' = need_alert \union {t}
        ELSE UNCHANGED need_alert

    /\ UNCHANGED alerting
    /\ UNCHANGED send_info
    /\ UNCHANGED notify_list
    /\ UNCHANGED <<next_val, state, version>>
    /\ UNCHANGED node_vars
    /\ UNCHANGED alert_enabled


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
        
        must_pushed(t) ==
            ~state_is_ok(t) => notify_by_type(t) # {}
                
        match_notify_list ==
            \A t \in Type:
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
    \A t \in Type:
        t \notin alerting <=> send_info[t].count = 0


SendCountLimit ==
    \A t \in Type: send_info[t].count <= max_send_count + max_send_count


SendStatusActiveWhenAlert ==
    \A t \in Type:
        t \in alerting <=> send_info[t].status = "Active"


AlwaysEnabledGetOrRetry ==
    \A t \in Type:
        ~state_is_ok(t) =>
            \/ pc = "Init" => ENABLED GetChangedKey(t)
            \/ send_info[t].count < max_send_count =>
                    ENABLED RetrySendAlert(t) /\ retry_update_cond(t)

====

------ MODULE AlertLogic ----
EXTENDS TLC, Naturals, Sequences

CONSTANTS Key, nil

VARIABLES version, changeset,
    state, alerting,
    send_info,
    notify_list, next_val, pc, local_key, local_status

vars == <<version, changeset,
    state, alerting,
    send_info,
    notify_list, next_val, pc, local_key, local_status>>

node_vars == <<pc, local_key, local_status>>


max_val == 35

max_send_count == 2

Version == 20..30

Value == 30..40

StateStatus == {"OK", "Failed"}

NullKey == Key \union {nil}

NullStatus == StateStatus \union {nil}

State == [val: Value, status: StateStatus]

Notify == [key: Key, status: StateStatus]

new_state == [val |-> 30, status |-> "OK"]

SendInfo == [count: Nat, status: {"Active", "Disabled"}]


TypeOK ==
    /\ version \in Version
    /\ changeset \subseteq Key
    /\ alerting \subseteq Key
    /\ send_info \in [Key -> SendInfo]
    /\ state \in [Key -> State]
    /\ notify_list \in Seq(Notify)
    /\ next_val \in Value
    /\ pc \in {"Init", "PushNotify"}
    /\ local_key \in NullKey
    /\ local_status \in NullStatus

init_send_info == [count |-> 0, status |-> "Disabled"]

Init ==
    /\ version = 20
    /\ changeset = {}
    /\ alerting = {}
    /\ send_info = [k \in Key |-> init_send_info]
    /\ state = [k \in Key |-> new_state]
    /\ notify_list = <<>>
    /\ next_val = 30
    /\ pc = "Init"
    /\ local_key = nil
    /\ local_status = nil


UpdateKey(k) ==
    LET
        update_cond(status) ==
            /\ k \notin changeset
            /\ IF status = "OK"
                THEN k \in alerting
                ELSE k \notin alerting

        need_clear(status) ==
            IF status = "OK"
                THEN k \notin alerting
                ELSE k \in alerting

        update_changeset(status) ==
            IF update_cond(status) THEN
                /\ changeset' = changeset \union {k}
                /\ version' = version + 1
            ELSE IF k \in changeset THEN
                /\ IF need_clear(status)
                    THEN changeset' = changeset \ {k}
                    ELSE UNCHANGED changeset
                /\ UNCHANGED version
            ELSE
                /\ UNCHANGED changeset
                /\ UNCHANGED version
    IN
    /\ next_val < max_val
    /\ next_val' = next_val + 1
    /\ \E status \in {"OK", "Failed"}:
        /\ state' = [state EXCEPT
            ![k].val = next_val',
            ![k].status = status]
        /\ update_changeset(status)
    /\ UNCHANGED alerting
    /\ UNCHANGED send_info
    /\ UNCHANGED notify_list
    /\ UNCHANGED node_vars


GetChangedKey(k) ==
    /\ pc = "Init"
    /\ k \in changeset
    /\ changeset' = changeset \ {k}

    /\ local_key' = k
    /\ local_status' = state[k].status
    /\ pc' = "PushNotify"
    /\ IF local_status' = "Failed"
        THEN
            /\ alerting' = alerting \union {k}
            /\ send_info' = [send_info EXCEPT
                    ![k].count = @ + 1,
                    ![k].status = "Active"]
        ELSE
            /\ alerting' = alerting \ {k}
            /\ send_info' = [send_info EXCEPT
                    ![k].count = 0,
                    ![k].status = "Disabled"]


    /\ UNCHANGED next_val
    /\ UNCHANGED notify_list
    /\ UNCHANGED <<state, version>>


PushNotify ==
    LET
        noti_status == local_status

        new_noti == [key |-> local_key, status |-> noti_status]
    IN
    /\ pc = "PushNotify"
    /\ pc' = "Init"
    /\ notify_list' = Append(notify_list, new_noti)

    /\ local_key' = nil \* clear local
    /\ local_status' = nil \* clear local

    /\ UNCHANGED alerting
    /\ UNCHANGED send_info
    /\ UNCHANGED <<changeset, version, state, next_val>>


retry_update_cond(k) ==
    /\ k \notin changeset
    /\ send_info[k].count < max_send_count

RetrySendAlert(k) ==
    /\ send_info[k].status = "Active"
    /\ IF retry_update_cond(k)
        THEN changeset' = changeset \union {k}
        ELSE UNCHANGED changeset

    /\ UNCHANGED alerting
    /\ UNCHANGED send_info
    /\ UNCHANGED notify_list
    /\ UNCHANGED <<next_val, state, version>>
    /\ UNCHANGED node_vars


TerminateCond ==
    /\ next_val = max_val
    /\ pc = "Init"
    /\ changeset = {}

Terminated ==
    /\ TerminateCond
    /\ UNCHANGED vars


Next ==
    \/ \E k \in Key:
        \/ UpdateKey(k)
        \/ RetrySendAlert(k)
        \/ GetChangedKey(k)
    \/ PushNotify
    \/ Terminated


Spec == Init /\ [][Next]_vars

FairSpec == Spec /\ WF_vars(Next)

AlwaysTerminate == <> TerminateCond


maxOfSet(set) ==
    CHOOSE x \in set: \A y \in set: y <= x

notify_by_key(k) ==
    {i \in DOMAIN notify_list: notify_list[i].key = k}

last_noti(k) ==
    notify_list[maxOfSet(notify_by_key(k))]


NotifyListReflectState ==
    LET
        match_cond(k) ==
            notify_by_key(k) # {} =>
                \/ last_noti(k).status = "Failed" /\ state[k].status = "Failed"
                \/ last_noti(k).status = "OK" /\ state[k].status = "OK"
        
        must_pushed(k) ==
            state[k].status = "Failed" => notify_by_key(k) # {}
                
        match_notify_list ==
            \A k \in Key:
                /\ match_cond(k)
                /\ must_pushed(k)
    IN
        TerminateCond => match_notify_list


AlertingMatchState ==
    LET
        alert_cond(k) ==
            /\ notify_by_key(k) # {}
            /\ last_noti(k).status = "Failed"

        match_cond ==
            \A k \in Key:
                k \in alerting <=> alert_cond(k)
    IN
        TerminateCond => match_cond


SendCountZeroForOK ==
    \A k \in Key:
        k \notin alerting <=> send_info[k].count = 0


SendCountLimit ==
    \A k \in Key: send_info[k].count <= max_send_count


SendStatusActiveWhenAlert ==
    \A k \in Key:
        k \in alerting <=> send_info[k].status = "Active"


AlwaysEnabledGetOrRetry ==
    \A k \in Key:
        state[k].status = "Failed" =>
            \/ pc = "Init" => ENABLED GetChangedKey(k)
            \/ send_info[k].count < max_send_count =>
                    ENABLED RetrySendAlert(k) /\ retry_update_cond(k)

====

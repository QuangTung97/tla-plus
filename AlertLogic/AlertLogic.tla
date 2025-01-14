------ MODULE AlertLogic ----
EXTENDS TLC, Naturals, Sequences

CONSTANTS Key, Node, nil

VARIABLES version, changeset, state, alerting,
    notify_list, next_val, pc, local_key, local_status

vars == <<version, changeset, state, alerting,
    notify_list, next_val, pc, local_key, local_status>>

node_vars == <<pc, local_key, local_status>>


max_val == 34

Version == 20..30

Value == 30..40

StateStatus == {"OK", "Failed"}

NullKey == Key \union {nil}

NullStatus == StateStatus \union {nil}

State == [val: Value, status: StateStatus]

Notify == [key: Key, status: {"Alert", "None"}]

new_state == [val |-> 30, status |-> "OK"]


TypeOK ==
    /\ version \in Version
    /\ changeset \subseteq Key
    /\ alerting \subseteq Key
    /\ state \in [Key -> State]
    /\ notify_list \in Seq(Notify)
    /\ next_val \in Value
    /\ pc \in [Node -> {"Init", "PushNotify"}]
    /\ local_key \in [Node -> NullKey]
    /\ local_status \in [Node -> NullStatus]


Init ==
    /\ version = 20
    /\ changeset = {}
    /\ alerting = {}
    /\ state = [k \in Key |-> new_state]
    /\ notify_list = <<>>
    /\ next_val = 30
    /\ pc = [n \in Node |-> "Init"]
    /\ local_key = [n \in Node |-> nil]
    /\ local_status = [n \in Node |-> nil]


UpdateKey(k) ==
    LET
        update_cond(status) ==
            /\ k \notin changeset
            /\ status = "Failed" \/ k \in alerting

        update_changeset(status) ==
            IF update_cond(status)
                THEN
                    /\ changeset' = changeset \union {k}
                    /\ version' = version + 1
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
    /\ UNCHANGED notify_list
    /\ UNCHANGED node_vars


GetChangedKey(n, k) ==
    /\ pc[n] = "Init"
    /\ k \in changeset
    /\ changeset' = changeset \ {k}

    /\ local_key' = [local_key EXCEPT ![n] = k]
    /\ local_status' = [local_status EXCEPT ![n] = state[k].status]
    /\ pc' = [pc EXCEPT ![n] = "PushNotify"]
    /\ IF local_status'[n] = "Failed"
        THEN alerting' = alerting \union {k}
        ELSE alerting' = alerting \ {k}

    /\ UNCHANGED next_val
    /\ UNCHANGED notify_list
    /\ UNCHANGED <<state, version>>


PushNotify(n) ==
    LET
        noti_status ==
            IF local_status[n] = "OK"
                THEN "None"
                ELSE "Alert"

        new_noti == [key |-> local_key[n], status |-> noti_status]
    IN
    /\ pc[n] = "PushNotify"
    /\ pc' = [pc EXCEPT ![n] = "Init"]
    /\ notify_list' = Append(notify_list, new_noti)

    /\ local_key' = [local_key EXCEPT ![n] = nil] \* clear local
    /\ local_status' = [local_status EXCEPT ![n] = nil] \* clear local

    /\ UNCHANGED alerting
    /\ UNCHANGED <<changeset, version, state, next_val>>


TerminateCond ==
    /\ next_val = max_val
    /\ \E n \in Node: pc[n] = "Init"
    /\ changeset = {}

Terminated ==
    /\ TerminateCond
    /\ UNCHANGED vars


Next ==
    \/ \E k \in Key:
        UpdateKey(k)
    \/ \E n \in Node:
        \/ \E k \in Key: GetChangedKey(n, k)
        \/ PushNotify(n)
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
                \/ last_noti(k).status = "Alert" /\ state[k].status = "Failed"
                \/ last_noti(k).status = "None" /\ state[k].status = "OK"
        
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
            /\ last_noti(k).status = "Alert"

        match_cond ==
            \A k \in Key:
                k \in alerting <=> alert_cond(k)
    IN
        TerminateCond => match_cond

====

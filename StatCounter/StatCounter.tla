------ MODULE StatCounter ----
EXTENDS TLC, Naturals, Sequences, FiniteSets

CONSTANTS Key, nil

VARIABLES counter, reset_counter, pending_added,
    db, pending, num_inc, pc, current_key, diff

vars == <<counter, reset_counter, pending_added,
    db, pending, num_inc, pc, current_key, diff>>


max_inc == 6

NullKey == Key \union {nil}

Range(f) == {f[x]: x \in DOMAIN f}

TypeOK ==
    /\ counter \in [Key -> Nat]
    /\ reset_counter \in [Key -> Nat]
    /\ pending_added \in [Key -> BOOLEAN]
    /\ pending \in Seq(Key)
    /\ db \in [Key -> Nat]
    /\ num_inc \in 0..max_inc
    /\ pc \in {"Init", "GetCounter", "UpdateDB"}
    /\ current_key \in NullKey
    /\ diff \in 0..max_inc


Init ==
    /\ counter = [k \in Key |-> 0]
    /\ reset_counter = [k \in Key |-> 0]
    /\ pending_added = [k \in Key |-> FALSE]
    /\ pending = <<>>
    /\ db = [k \in Key |-> 0]
    /\ num_inc = 0
    /\ pc = "Init"
    /\ current_key = nil
    /\ diff = 0


IncreaseCounter(k) ==
    /\ num_inc < max_inc
    /\ num_inc' = num_inc + 1
    /\ counter' = [counter EXCEPT ![k] = @ + 1]
    /\ reset_counter' = [reset_counter EXCEPT ![k] = @ + 1]
    /\ IF pending_added[k]
        THEN
            /\ UNCHANGED pending
            /\ UNCHANGED pending_added
        ELSE
            /\ pending' = Append(pending, k)
            /\ pending_added' = [pending_added EXCEPT ![k] = TRUE]
    /\ UNCHANGED db
    /\ UNCHANGED <<pc, current_key, diff>>


GetFromPending ==
    /\ pc = "Init"
    /\ Len(pending) > 0
    /\ pc' = "GetCounter"
    /\ current_key' = Head(pending)
    /\ pending' = Tail(pending)
    /\ UNCHANGED diff
    /\ UNCHANGED <<counter, reset_counter, pending_added>>
    /\ UNCHANGED db
    /\ UNCHANGED num_inc


GetCounter ==
    /\ pc = "GetCounter"
    /\ pc' = "UpdateDB"
    /\ diff' = reset_counter[current_key]
    /\ reset_counter' = [reset_counter EXCEPT ![current_key] = 0]
    /\ pending_added' = [pending_added EXCEPT ![current_key] = FALSE]
    /\ UNCHANGED <<counter, pending, num_inc>>
    /\ UNCHANGED current_key
    /\ UNCHANGED db


UpdateDB ==
    /\ pc = "UpdateDB"
    /\ pc' = "Init"
    /\ db' = [db EXCEPT ![current_key] = @ + diff]
    /\ diff' = 0
    /\ current_key' = nil
    /\ UNCHANGED num_inc
    /\ UNCHANGED <<counter, pending, pending_added>>
    /\ UNCHANGED reset_counter


stoppingCond ==
    /\ pending = <<>>
    /\ pc = "Init"

TerminateCond ==
    /\ num_inc = max_inc
    /\ stoppingCond

Terminated ==
    /\ TerminateCond
    /\ UNCHANGED vars


Next ==
    \/ \E k \in Key:
        \/ IncreaseCounter(k)
    \/ GetFromPending
    \/ GetCounter
    \/ UpdateDB
    \/ Terminated


Spec == Init /\ [][Next]_vars

FairSpec == Spec /\ WF_vars(Next)


AlwaysTerminate == <> TerminateCond


DBMatchCounter ==
    stoppingCond => db = counter


InitInv ==
    pc = "Init" =>
        /\ current_key = nil
        /\ diff = 0


PendingNoDuplicate ==
    LET
        keys == Range(pending)
    IN
        Cardinality(keys) = Len(pending)

====

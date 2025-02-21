------ MODULE LeaderLease ----
EXTENDS TLC, Naturals, Sequences

CONSTANTS Node, nil, max_epoch, max_counter

VARIABLES zk_leader, zk_epoch, zk_counter, zk_request,
    local_time, local_leader, local_epoch,
    local_current, local_up_count, expected_count,
    global_count

vars == <<zk_leader, zk_epoch, zk_counter, zk_request,
    local_time, local_leader, local_epoch,
    local_current, local_up_count, expected_count,
    global_count
>>

-----------------------------------------------------------------------------

NullNode == Node \union {nil}

Epoch == 20..29

Counter == 30..39

NullCounter == Counter \union {nil}

Time == 50..70

init_time == {51, 55, 57}

Request == [epoch: Epoch, inc: 1..10]

-----------------------------------------------------------------------------

TypeOK ==
    /\ zk_leader \in NullNode
    /\ zk_epoch \in Epoch
    /\ zk_counter \in Counter
    /\ zk_request \in Seq(Request)
    /\ local_time \in [Node -> Time]
    /\ local_leader \in [Node -> NullNode]
    /\ local_epoch \in [Node -> Epoch]
    /\ local_current \in [Node -> NullCounter]
    /\ local_up_count \in [Node -> NullCounter]
    /\ expected_count \in [Node -> NullCounter]
    /\ global_count \in Seq(Counter)


Init ==
    /\ zk_leader = nil
    /\ zk_epoch = 20
    /\ zk_counter = 30
    /\ zk_request = <<>>
    /\ local_time \in [Node -> init_time]
    /\ local_leader = [n \in Node |-> nil]
    /\ local_epoch = [n \in Node |-> 20]
    /\ local_current = [n \in Node |-> nil]
    /\ local_up_count = [n \in Node |-> nil]
    /\ expected_count = [n \in Node |-> nil]
    /\ global_count = <<30>>

-----------------------------------------------------------------------------

local_vars == <<
    local_epoch, local_leader, local_time,
    local_current, local_up_count
>>

zk_vars == <<zk_leader, zk_epoch, zk_counter>>


ElectLeader(n) ==
    /\ zk_leader # n
    /\ zk_epoch < max_epoch
    /\ zk_leader' = n
    /\ zk_epoch' = zk_epoch + 1

    /\ UNCHANGED zk_counter
    /\ UNCHANGED zk_request
    /\ UNCHANGED local_vars
    /\ UNCHANGED expected_count
    /\ UNCHANGED global_count


WatchChange(n) ==
    /\ local_epoch[n] < zk_epoch
    /\ local_epoch' = [local_epoch EXCEPT ![n] = zk_epoch]
    /\ local_leader' = [local_leader EXCEPT ![n] = zk_leader]
    /\ local_up_count' = [local_up_count EXCEPT ![n] = zk_counter]
    /\ local_current' = [local_current EXCEPT ![n] = zk_counter]
    /\ expected_count' = [expected_count EXCEPT ![n] = zk_counter]
    /\ UNCHANGED local_time
    /\ UNCHANGED zk_vars
    /\ UNCHANGED zk_request
    /\ UNCHANGED global_count


WatchCounter(n) ==
    /\ local_leader[n] # nil
    /\ local_up_count[n] < zk_counter
    /\ local_up_count' = [local_up_count EXCEPT ![n] = zk_counter]
    /\ UNCHANGED <<local_leader, local_epoch, local_current>>
    /\ UNCHANGED local_time
    /\ UNCHANGED expected_count
    /\ UNCHANGED zk_vars
    /\ UNCHANGED zk_request
    /\ UNCHANGED global_count


is_leader(n) ==
    local_leader[n] = n


diff_range == 3

PrepareInc(n) ==
    LET
        diff == 1

        new_req == [
            epoch |-> local_epoch[n],
            inc |-> diff
        ]
    IN
    /\ is_leader(n)
    /\ expected_count[n] < local_current[n] + diff_range
    /\ expected_count[n] < max_counter

    /\ zk_request' = Append(zk_request, new_req)
    /\ expected_count' = [expected_count EXCEPT ![n] = @ + diff]

    /\ UNCHANGED local_vars
    /\ UNCHANGED zk_vars
    /\ UNCHANGED global_count


ZkConsumeReq ==
    LET
        req == zk_request[1]
    IN
    /\ zk_request # <<>>

    /\ zk_request' = Tail(zk_request)
    /\ IF req.epoch = zk_epoch
        THEN zk_counter' = zk_counter + req.inc
        ELSE UNCHANGED zk_counter

    /\ UNCHANGED <<zk_epoch, zk_leader>>
    /\ UNCHANGED local_vars
    /\ UNCHANGED expected_count
    /\ UNCHANGED global_count


IncreaseLocalCounter(n) ==
    LET
        new_count == local_current[n] + 1
    IN
    /\ is_leader(n)
    /\ local_current[n] < local_up_count[n]

    /\ local_current' = [local_current EXCEPT ![n] = new_count]
    /\ global_count' = Append(global_count, new_count)

    /\ UNCHANGED <<local_epoch, local_leader, local_time>>
    /\ UNCHANGED local_up_count
    /\ UNCHANGED expected_count
    /\ UNCHANGED zk_vars
    /\ UNCHANGED zk_request

-----------------------------------------------------------------------------

TerminateCond ==
    /\ TRUE

Terminated ==
    /\ TerminateCond
    /\ UNCHANGED vars

Next ==
    \/ \E n \in Node:
        \/ ElectLeader(n)
        \/ WatchChange(n)
        \/ WatchCounter(n)
        \/ PrepareInc(n)
        \/ IncreaseLocalCounter(n)
    \/ ZkConsumeReq
    \/ Terminated

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------

GlobalCountMustBeIncreasing ==
    LET
        n == Len(global_count) - 1
    IN
    \A i \in 1..n: global_count[i] < global_count[i + 1]

====

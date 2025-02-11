------ MODULE JobPool ----
EXTENDS TLC, Naturals, Sequences, FiniteSets

CONSTANTS Node, Key, nil, max_val, max_move

VARIABLES running_set, pending_map, pending_queue,
    closed, last_val, next_val,
    pc, wait_queue, consume_chan,
    local_key, local_val, handled_key,
    num_move

vars == <<running_set, pending_map, pending_queue,
    closed, last_val, next_val,
    pc, wait_queue, consume_chan,
    local_key, local_val, handled_key,
    num_move
>>

aux_vars == <<num_move>>

-------------------------------------------------------

NullKey == Key \union {nil}

Value == 20..29

NullValue == Value \union {nil}

PendingInfo == [
    val: Value,
    in_queue: BOOLEAN
]

NullPendingInfo == PendingInfo \union {nil}

KeyVal == [key: Key, val: Value]

Channel == [
    data: Seq(KeyVal),
    closed: BOOLEAN
]

init_chan == [data |-> <<>>, closed |-> FALSE]

Range(f) == {f[x]: x \in DOMAIN f}

PC == {"Init", "WaitOnChan", "HandleKey", "ClearRunning", "Terminated"}

-------------------------------------------------------

TypeOK ==
    /\ running_set \subseteq Key
    /\ pending_map \in [Key -> NullPendingInfo]
    /\ pending_queue \in Seq(Key)
    /\ closed \in BOOLEAN
    /\ last_val \in [Key -> Value]
    /\ next_val \in Value
    /\ pc \in [Node -> PC]
    /\ consume_chan \in [Node -> Channel]
    /\ wait_queue \in Seq(Node)
    /\ handled_key \in [Key -> Seq(Value)]
    /\ local_key \in [Node -> NullKey]
    /\ local_val \in [Node -> NullValue]
    /\ num_move \in 0..max_move


Init ==
    /\ running_set = {}
    /\ pending_map = [k \in Key |-> nil]
    /\ pending_queue = <<>>
    /\ closed = FALSE
    /\ last_val = [k \in Key |-> 20]
    /\ next_val = 20
    /\ pc = [n \in Node |-> "Init"]
    /\ consume_chan = [n \in Node |-> init_chan]
    /\ wait_queue = <<>>
    /\ handled_key = [k \in Key |-> <<>>]
    /\ local_key = [n \in Node |-> nil]
    /\ local_val = [n \in Node |-> nil]
    /\ num_move = 0


pushToWaitQueueIfNotEmpty(k, val, else_stmt) ==
    LET
        new_kv == [key |-> k, val |-> val]

        n == wait_queue[1]

        handle_wait_queue_non_empty ==
            /\ wait_queue' = Tail(wait_queue)
            /\ consume_chan' = [consume_chan EXCEPT
                    ![n].data = Append(@, new_kv)
                ]
            /\ running_set' = running_set \union {k}
            /\ pending_map' = [pending_map EXCEPT ![k] = nil]
            /\ UNCHANGED pending_queue
    IN
    IF wait_queue # <<>>
        THEN handle_wait_queue_non_empty
        ELSE else_stmt


upsert_pending(new_val, in_queue) ==
    [val |-> new_val, in_queue |-> in_queue]

StartJob(k) ==
    LET
        handle_running ==
            /\ pending_map' = [pending_map EXCEPT
                    ![k] = upsert_pending(next_val', FALSE)
                ]
            /\ UNCHANGED pending_queue
            /\ UNCHANGED wait_queue
            /\ UNCHANGED consume_chan
            /\ UNCHANGED running_set

        update_map ==
            /\ IF pending_map[k] = nil
                THEN pending_queue' = Append(pending_queue, k)
                ELSE UNCHANGED pending_queue
            /\ pending_map' = [pending_map EXCEPT
                    ![k] = upsert_pending(next_val', TRUE)
                ]
            /\ UNCHANGED wait_queue
            /\ UNCHANGED consume_chan
            /\ UNCHANGED running_set
    IN
    /\ next_val < max_val
    /\ next_val' = next_val + 1
    /\ last_val' = [last_val EXCEPT ![k] = next_val']
    /\ ~closed

    /\ IF k \in running_set
        THEN handle_running
        ELSE pushToWaitQueueIfNotEmpty(k, next_val', update_map)

    /\ UNCHANGED handled_key
    /\ UNCHANGED <<pc, local_key, local_val>>
    /\ UNCHANGED closed
    /\ UNCHANGED aux_vars


MoveToHead(k) ==
    LET
        filter_fn(x) == x # k

        removed == SelectSeq(pending_queue, filter_fn)
    IN
    /\ num_move < max_move
    /\ num_move' = num_move + 1
    /\ pending_map[k] # nil
    /\ pending_map[k].in_queue
    /\ pending_queue[1] # k

    /\ pending_queue' = <<k>> \o removed

    /\ UNCHANGED <<consume_chan, wait_queue>>
    /\ UNCHANGED <<pending_map, running_set>>
    /\ UNCHANGED handled_key
    /\ UNCHANGED <<pc, local_key, local_val>>
    /\ UNCHANGED next_val
    /\ UNCHANGED last_val
    /\ UNCHANGED closed


getPendingKeyValue(n) ==
    LET
        k == pending_queue[1]
    IN
        /\ local_key' = [local_key EXCEPT ![n] = k]
        /\ local_val' = [local_val EXCEPT ![n] = pending_map[k].val]

        /\ pending_queue' = Tail(pending_queue)
        /\ pending_map' = [pending_map EXCEPT ![k] = nil]
        /\ running_set' = running_set \union {k}

        /\ UNCHANGED consume_chan
        /\ UNCHANGED wait_queue


SetWaitChan(n) ==
    /\ pc[n] = "Init"

    /\ IF pending_queue # <<>> THEN
            /\ getPendingKeyValue(n)
            /\ pc' = [pc EXCEPT ![n] = "HandleKey"]
        ELSE IF ~closed THEN
            /\ pc' = [pc EXCEPT ![n] = "WaitOnChan"]
            /\ wait_queue' = Append(wait_queue, n)
            /\ UNCHANGED consume_chan
            /\ UNCHANGED pending_map
            /\ UNCHANGED pending_queue
            /\ UNCHANGED running_set
            /\ UNCHANGED <<local_key, local_val>>
        ELSE
            /\ pc' = [pc EXCEPT ![n] = "Terminated"]
            /\ UNCHANGED wait_queue
            /\ UNCHANGED consume_chan
            /\ UNCHANGED pending_map
            /\ UNCHANGED pending_queue
            /\ UNCHANGED running_set
            /\ UNCHANGED <<local_key, local_val>>

    /\ UNCHANGED handled_key
    /\ UNCHANGED last_val
    /\ UNCHANGED next_val
    /\ UNCHANGED aux_vars
    /\ UNCHANGED closed


WaitOnChan(n) ==
    LET
        e == consume_chan[n].data[1]

        goto_handle_key ==
            /\ consume_chan[n].data # <<>>
            /\ pc' = [pc EXCEPT ![n] = "HandleKey"]

            /\ consume_chan' = [consume_chan EXCEPT
                    ![n].data = Tail(@)
                ]
            /\ local_key' = [local_key EXCEPT ![n] = e.key]
            /\ local_val' = [local_val EXCEPT ![n] = e.val]

        goto_terminated ==
            /\ consume_chan[n].closed
            /\ consume_chan[n].data = <<>>
            /\ pc' = [pc EXCEPT ![n] = "Terminated"]
            /\ local_key' = [local_key EXCEPT ![n] = nil]
            /\ local_val' = [local_val EXCEPT ![n] = nil]
            /\ UNCHANGED consume_chan

    IN
    /\ pc[n] = "WaitOnChan"

    /\ \/ goto_handle_key
       \/ goto_terminated

    /\ UNCHANGED <<next_val, last_val>>
    /\ UNCHANGED handled_key
    /\ UNCHANGED <<pending_map, pending_queue, running_set, wait_queue>>
    /\ UNCHANGED closed
    /\ UNCHANGED aux_vars


HandleKey(n) ==
    LET
        k == local_key[n]
        val == local_val[n]
    IN
    /\ pc[n] = "HandleKey"
    /\ pc' = [pc EXCEPT ![n] = "ClearRunning"]

    /\ handled_key' = [handled_key EXCEPT ![k] = Append(@, val)]

    /\ UNCHANGED <<local_key, local_val>>
    /\ UNCHANGED last_val
    /\ UNCHANGED consume_chan
    /\ UNCHANGED wait_queue
    /\ UNCHANGED closed
    /\ UNCHANGED next_val
    /\ UNCHANGED <<pending_queue, pending_map, running_set>>
    /\ UNCHANGED aux_vars


ClearRunning(n) ==
    LET
        k == local_key[n]

        new_set == running_set \ {k}

        else_stmt ==
            /\ running_set' = new_set
            /\ pending_queue' = Append(pending_queue, k)
            /\ pending_map' = [pending_map EXCEPT ![k].in_queue = TRUE]
            /\ UNCHANGED <<wait_queue, consume_chan>>
    IN
    /\ pc[n] = "ClearRunning"
    /\ pc' = [pc EXCEPT ![n] = "Init"]

    /\ IF pending_map[k] # nil
        THEN
            /\ pushToWaitQueueIfNotEmpty(k, pending_map[k].val, else_stmt)
        ELSE
            /\ running_set' = new_set
            /\ UNCHANGED <<pending_map, pending_queue>>
            /\ UNCHANGED <<wait_queue, consume_chan>>

    /\ local_key' = [local_key EXCEPT ![n] = nil]
    /\ local_val' = [local_val EXCEPT ![n] = nil]

    /\ UNCHANGED <<next_val, last_val>>
    /\ UNCHANGED handled_key
    /\ UNCHANGED closed
    /\ UNCHANGED aux_vars


Shutdown ==
    LET
        close_set == Range(wait_queue)

        do_close_ch(n, old) ==
            IF n \in close_set
                THEN [old EXCEPT !.closed = TRUE]
                ELSE old

        close_all_wait_queue ==
            consume_chan' = [
                n \in Node |-> do_close_ch(n, consume_chan[n])
            ]
    IN
    /\ ~closed
    /\ closed' = TRUE
    /\ close_all_wait_queue
    /\ wait_queue' = <<>>

    /\ UNCHANGED <<last_val, next_val>>
    /\ UNCHANGED <<pending_map, pending_queue, running_set>>
    /\ UNCHANGED <<pc, local_key, local_val>>
    /\ UNCHANGED handled_key
    /\ UNCHANGED aux_vars

-------------------------------------------------------

StopCond ==
    \A n \in Node:
        \/ pc[n] = "Terminated"
        \/ /\ pc[n] = "WaitOnChan"
           /\ consume_chan[n].data = <<>>

TerminateCond ==
    /\ \A n \in Node: pc[n] = "Terminated"
    /\ closed

Terminated ==
    /\ TerminateCond
    /\ UNCHANGED vars

-------------------------------------------------------

Next ==
    \/ \E k \in Key:
        \/ StartJob(k)
        \/ MoveToHead(k)
    \/ \E n \in Node:
        \/ SetWaitChan(n)
        \/ WaitOnChan(n)
        \/ HandleKey(n)
        \/ ClearRunning(n)
    \/ Shutdown
    \/ Terminated

Spec == Init /\ [][Next]_vars

FairSpec == Spec /\ WF_vars(Next)

-------------------------------------------------------

AlwaysTerminate == <> TerminateCond


seqNotDuplicated(seq) ==
    Len(seq) = Cardinality(Range(seq))


QueueNotContainDuplicate ==
    Len(pending_queue) = Cardinality(Range(pending_queue))


Inv ==
    LET
        handled_last(k) == handled_key[k][Len(handled_key[k])]

        cond ==
            \A k \in Key:
                last_val[k] > 20 => handled_last(k) = last_val[k]
    IN
        StopCond => cond


HandledKeyNoDuplicate ==
    \A k \in Key:
        LET
            keys == handled_key[k]
        IN
            seqNotDuplicated(keys)


MustNotHandleSameKeyConcurrently ==
    LET
        running_nodes == {n \in Node: pc[n] = "HandleKey"}

        running_keys == {local_key[n]: n \in running_nodes}
    IN
        Cardinality(running_keys) = Cardinality(running_nodes)


WaitQueueNotDuplicate ==
    Len(wait_queue) = Cardinality(Range(wait_queue))


PendingQueueAndRunningDisjoint ==
    Range(pending_queue) \intersect running_set = {}


PendingMapIsSubsetPendingQueueAndRunningSet ==
    LET
        cmp_set == {k \in Key: pending_map[k] # nil}

        union_set == Range(pending_queue) \union running_set
    IN
        cmp_set \subseteq union_set


PendingQueueIsSubsetOfPendingMap ==
    LET
        cmp_set == {k \in Key: pending_map[k] # nil}
    IN
        Range(pending_queue) \subseteq cmp_set


ChannelLenNotGreaterThanOne ==
    \A n \in Node:
        Len(consume_chan[n].data) <= 1


InQueueMatchPendingQueue ==
    LET
        is_in_queue(k) ==
            /\ pending_map[k] # nil
            /\ pending_map[k].in_queue
    IN
    \A k \in Key:
        is_in_queue(k) <=> k \in Range(pending_queue)


TerminateCondIsStopCond ==
    TerminateCond => StopCond


WaitQueueNonEmptyWhenPendingQueueEmpty ==
    wait_queue # <<>> => pending_queue = <<>>


canNotPushToChanWhenClosedStep ==
    \A n \in Node:
        consume_chan[n].closed =>
            Len(consume_chan'[n].data) <= Len(consume_chan[n].data)

CanNotPushToChanWhenClosed ==
    [][canNotPushToChanWhenClosedStep]_consume_chan


PendingMapMustBeUpToDate ==
    \A k \in Key:
        pending_map[k] # nil => pending_map[k].val = last_val[k]


ReverseInv ==
    \A k \in Key:
        k \in running_set => pending_map[k] = nil


====

------ MODULE MemCache ----
EXTENDS TLC, Naturals

CONSTANTS Key, Node, nil

VARIABLES pc, db, locked, cache, next_cas,
    local_key, local_item

vars == <<pc, db, locked, cache, next_cas,
    local_key, local_item>>

----------------------------------------------------------------------------

NullKey == Key \union {nil}

UpdatePC == {
    "LockUpdateCache", "UpdateCache"
}

ReadonlyPC == {
    "Init", "GetFromCache", "HandleGetNil",
    "GetFromDB", "UseItem",
    "LockSetCache", "SetBackToCache",
    "Terminated"
}

PC == ReadonlyPC \union UpdatePC

Value == 20..29

NullValue == Value \union {nil}

CAS == 40..49

NullCAS == CAS \union {nil}

CacheVal == [
    cas: CAS,
    val: NullValue
]

NullCacheVal == CacheVal \union {nil}

CacheValCASNull == [
    cas: NullCAS,
    val: NullValue
]

----------------------------------------------------------------------------

TypeOK ==
    /\ pc \in [Node -> PC]
    /\ db \in [Key -> Value]
    /\ locked \in [Key -> BOOLEAN]
    /\ cache \in [Key -> NullCacheVal]
    /\ next_cas \in CAS
    /\ local_key \in [Node -> NullKey]
    /\ local_item \in [Node -> (CacheValCASNull \union {nil})]

Init ==
    /\ pc = [n \in Node |-> "Init"]
    /\ db = [k \in Key |-> 20]
    /\ locked = [k \in Key |-> FALSE]
    /\ cache = [k \in Key |-> nil]
    /\ next_cas = 40
    /\ local_key = [n \in Node |-> nil]
    /\ local_item = [n \in Node |-> nil]

----------------------------------------------------------------------------

goto(n, l) ==
    pc' = [pc EXCEPT ![n] = l]

lock_key(k) ==
    /\ ~locked[k]
    /\ locked' = [locked EXCEPT ![k] = TRUE]

unlock_key(k) ==
    /\ locked' = [locked EXCEPT ![k] = FALSE]


CacheGet(n, k) ==
    /\ pc[n] = "Init"
    /\ lock_key(k)
    /\ goto(n, "GetFromCache")
    /\ local_key' = [local_key EXCEPT ![n] = k]
    /\ UNCHANGED local_item
    /\ UNCHANGED <<cache, next_cas>>
    /\ UNCHANGED db


GetFromCache(n) ==
    LET
        k == local_key[n]

        handle_nil ==
            /\ goto(n, "HandleGetNil")
            /\ UNCHANGED local_item
            /\ UNCHANGED locked

        need_get_from_db ==
            /\ goto(n, "GetFromDB")
            /\ local_item' = [local_item EXCEPT ![n] = cache[k]]
            /\ unlock_key(k)

        return_item ==
            /\ goto(n, "UseItem")
            /\ local_item' = [local_item EXCEPT ![n] = cache[k]]
            /\ unlock_key(k)
    IN
    /\ pc[n] = "GetFromCache"

    /\ IF cache[k] = nil THEN
            handle_nil
        ELSE IF cache[k].val = nil THEN
            need_get_from_db
        ELSE
            return_item

    /\ UNCHANGED <<cache, next_cas>>
    /\ UNCHANGED local_key
    /\ UNCHANGED db


HandleGetNil(n) ==
    LET
        k == local_key[n]

        new_item == [
            cas |-> next_cas',
            val |-> nil
        ]
    IN
    /\ pc[n] = "HandleGetNil"
    /\ goto(n, "GetFromDB")
    /\ unlock_key(k)

    /\ next_cas' = next_cas + 1
    /\ cache' = [cache EXCEPT ![k] = new_item]
    /\ local_item' = [local_item EXCEPT ![n] = new_item]

    /\ UNCHANGED local_key
    /\ UNCHANGED db


GetFromDB(n) ==
    LET
        k == local_key[n]
    IN
    /\ pc[n] = "GetFromDB"
    /\ goto(n, "LockSetCache")

    /\ local_item' = [local_item EXCEPT ![n].val = db[k]]

    /\ UNCHANGED locked
    /\ UNCHANGED <<cache, next_cas>>
    /\ UNCHANGED local_key
    /\ UNCHANGED db


LockSetCache(n) ==
    LET
        k == local_key[n]
    IN
    /\ pc[n] = "LockSetCache"
    /\ goto(n, "SetBackToCache")
    /\ lock_key(k)

    /\ UNCHANGED local_item
    /\ UNCHANGED <<cache, next_cas>>
    /\ UNCHANGED local_key
    /\ UNCHANGED db


SetBackToCache(n) ==
    LET
        k == local_key[n]

        update_cond ==
            /\ cache[k] # nil
            /\ cache[k].cas = local_item[n].cas
    IN
    /\ pc[n] = "SetBackToCache"
    /\ goto(n, "UseItem")
    /\ unlock_key(k)

    /\ IF update_cond
        THEN cache' = [cache EXCEPT ![k] = local_item[n]]
        ELSE UNCHANGED cache

    /\ UNCHANGED next_cas
    /\ UNCHANGED local_item
    /\ UNCHANGED local_key
    /\ UNCHANGED db


UseItem(n) ==
    /\ pc[n] = "UseItem"
    /\ goto(n, "Terminated")

    /\ UNCHANGED <<local_key, local_item>>
    /\ UNCHANGED <<cache, next_cas>>
    /\ UNCHANGED locked
    /\ UNCHANGED db


no_other_updating ==
    \A n \in Node: pc[n] \notin UpdatePC

UpdateDB(n, k) ==
    LET
        new_val == db[k] + 1

        new_item == [cas |-> nil, val |-> new_val]
    IN
    /\ pc[n] = "Init"
    /\ no_other_updating

    /\ goto(n, "LockUpdateCache")
    /\ db' = [db EXCEPT ![k] = new_val]

    /\ local_key' = [local_key EXCEPT ![n] = k]
    /\ local_item' = [local_item EXCEPT ![n] = new_item]

    /\ UNCHANGED <<cache, next_cas>>
    /\ UNCHANGED locked


LockUpdateCache(n) ==
    LET
        k == local_key[n]
    IN
    /\ pc[n] = "LockUpdateCache"
    /\ goto(n, "UpdateCache")
    /\ lock_key(k)

    /\ UNCHANGED <<local_key, local_item>>
    /\ UNCHANGED <<cache, next_cas>>
    /\ UNCHANGED db


UpdateCache(n) ==
    LET
        k == local_key[n]

        new_item == [
            cas |-> next_cas',
            val |-> local_item[n].val
        ]
    IN
    /\ pc[n] = "UpdateCache"
    /\ goto(n, "Terminated")
    /\ unlock_key(k)

    /\ next_cas' = next_cas + 1
    /\ cache' = [cache EXCEPT ![k] = new_item]

    /\ UNCHANGED <<local_key, local_item>>
    /\ UNCHANGED db


CacheLRU(k) ==
    /\ cache[k] # nil
    /\ cache' = [cache EXCEPT ![k] = nil]

    /\ UNCHANGED <<pc, local_key, local_item>>
    /\ UNCHANGED next_cas
    /\ UNCHANGED locked
    /\ UNCHANGED db

----------------------------------------------------------------------------

TerminateCond ==
    /\ \A k \in Key: ~locked[k]
    /\ \A n \in Node: pc[n] = "Terminated"

Terminated ==
    /\ TerminateCond
    /\ UNCHANGED vars

Next ==
    \/ \E n \in Node, k \in Key:
        \/ CacheGet(n, k)
        \/ UpdateDB(n, k)

    \/ \E n \in Node:
        \/ GetFromCache(n)
        \/ HandleGetNil(n)
        \/ GetFromDB(n)
        \/ LockSetCache(n)
        \/ SetBackToCache(n)
        \/ UseItem(n)

        \/ LockUpdateCache(n)
        \/ UpdateCache(n)

    \/ \E k \in Key: CacheLRU(k)

    \/ Terminated

Spec == Init /\ [][Next]_vars

FairSpec == Spec /\ WF_vars(Next)

----------------------------------------------------------------------------

AlwaysTerminate == <> TerminateCond

LockedStateInv ==
    LET
        non_locked == {
            "Init", "GetFromDB", "UseItem",
            "LockSetCache",
            "LockUpdateCache",
            "Terminated"
        }

        locked_pc == PC \ non_locked

        is_locked(n) ==
            /\ local_key[n] # nil
            /\ locked[local_key[n]]

        no_node_is_locked(k) ==
            LET
                inverse_cond(n) ==
                    /\ pc[n] \in locked_pc
                    /\ local_key[n] = k
            IN
            \A n \in Node: ~inverse_cond(n)
    IN
    /\ \A n \in Node: pc[n] \in locked_pc => is_locked(n)
    /\ \A k \in Key: ~locked[k] => no_node_is_locked(k)


UseItemWithData ==
    \A n \in Node:
        pc[n] = "UseItem" => local_item[n].val # nil


DBMatchCache ==
    LET
        cond(k) ==
            \/ cache[k] = nil
            \/ cache[k].val = db[k]
    IN
    TerminateCond => \A k \in Key: cond(k)

====

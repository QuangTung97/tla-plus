---- MODULE Memcached ----
EXTENDS TLC, Naturals

CONSTANTS Node, Key, HashSlot, Page, Offset, Slab, nil

VARIABLES
    key_to_slot,
    pc, local_key, local_slab, local_item,
    free_pages, hash_slot_lock,
    slab_lock, slab_free_items, slab_inuse_items,
    item_map, hash_map,
    stop_cmd

const_vars == <<
    key_to_slot
>>

local_vars == <<
    pc, local_key, local_slab, local_item
>>

slab_vars == <<
    slab_lock, slab_free_items, slab_inuse_items
>>

vars == <<
    const_vars,
    local_vars,
    free_pages, hash_slot_lock,
    slab_vars,
    item_map, hash_map,
    stop_cmd
>>

------------------------------------------------------------------

Null(S) == S \union {nil}

Item == Page \X Offset

ItemData == [
    key: Key,
    slab: Slab,
    refcount: Nat,
    deleted: BOOLEAN
]

PC == {
    "Init", "LockSlot",
    "DeletePrevKey", "GetFreePage",
    "EvictSlab", "SetItem",
    "GetDecRef"
}

------------------------------------------------------------------

TypeOK ==
    /\ key_to_slot \in [Key -> HashSlot]
    /\ free_pages \subseteq Page
    /\ hash_slot_lock \in [HashSlot -> Nat]

    /\ slab_lock \in [Slab -> Nat]
    /\ slab_free_items \in [Slab -> SUBSET Item]
    /\ slab_inuse_items \in [Slab -> SUBSET Item]
    /\ item_map \in [Item -> Null(ItemData)]
    /\ hash_map \in [Key -> Null(Item)]

    /\ pc \in [Node -> PC]
    /\ local_key \in [Node -> Null(Key)]
    /\ local_slab \in [Node -> Null(Slab)]
    /\ local_item \in [Node -> Null(Item)]

    /\ stop_cmd \in BOOLEAN

Init ==
    /\ key_to_slot \in [Key -> HashSlot]
    /\ free_pages = Page
    /\ hash_slot_lock = [h \in HashSlot |-> 0]

    /\ slab_lock = [s \in Slab |-> 0]
    /\ slab_free_items = [s \in Slab |-> {}]
    /\ slab_inuse_items = [s \in Slab |-> {}]
    /\ item_map = [i \in Item |-> nil]
    /\ hash_map = [k \in Key |-> nil]

    /\ pc = [n \in Node |-> "Init"]
    /\ local_key = [n \in Node |-> nil]
    /\ local_slab = [n \in Node |-> nil]
    /\ local_item = [n \in Node |-> nil]

    /\ stop_cmd = FALSE

------------------------------------------------------------------

set_local(n, var, x) ==
    var' = [var EXCEPT ![n] = x]

goto(n, l) ==
    pc' = [pc EXCEPT ![n] = l]

node_logic_unchanged ==
    /\ UNCHANGED const_vars
    /\ UNCHANGED <<local_key, local_slab, local_item>>
    /\ UNCHANGED stop_cmd

------------------------------------------------------------------

PutKey(n, k, s) ==
    /\ ~stop_cmd
    /\ pc[n] = "Init"
    /\ goto(n, "LockSlot")
    /\ set_local(n, local_key, k)
    /\ set_local(n, local_slab, s)

    /\ UNCHANGED local_item
    /\ UNCHANGED <<free_pages, hash_slot_lock>>
    /\ UNCHANGED slab_vars
    /\ UNCHANGED <<item_map, hash_map>>
    /\ UNCHANGED const_vars
    /\ UNCHANGED stop_cmd

------------------------------------------------------------------

do_lock_hash_slot(h) ==
    /\ hash_slot_lock[h] = 0
    /\ hash_slot_lock' = [hash_slot_lock EXCEPT ![h] = @ + 1]

------------------------

LockSlot(n) ==
    LET
        k == local_key[n]
        h == key_to_slot[k]

        prev_exist ==
            hash_map[k] # nil

        go_next ==
            IF prev_exist THEN
                goto(n, "DeletePrevKey")
            ELSE
                goto(n, "GetFreePage")
    IN
    /\ pc[n] = "LockSlot"

    /\ do_lock_hash_slot(h)
    /\ go_next

    /\ UNCHANGED free_pages
    /\ UNCHANGED slab_vars
    /\ UNCHANGED <<item_map, hash_map>>
    /\ node_logic_unchanged

------------------------------------------------------------------

do_delete_item(it) ==
    LET
        s == item_map[it].slab
    IN
    /\ item_map' = [item_map EXCEPT ![it] = nil]
    /\ slab_free_items' = [slab_free_items EXCEPT ![s] = @ \union {it}]
    /\ slab_inuse_items' = [slab_inuse_items EXCEPT ![s] = @ \ {it}]

dec_refcount_or_delete(it, with_delete) ==
    LET
        k == item_map[it].key
        s == item_map[it].slab

        can_delete ==
            item_map[it].refcount = 1

        on_dec_only ==
            /\ item_map' = [item_map EXCEPT
                    ![it].refcount = @ - 1,
                    ![it].deleted = @ \/ with_delete
                ]
            /\ UNCHANGED slab_free_items
            /\ UNCHANGED slab_inuse_items
    IN
    /\ slab_lock[s] = 0 \* slab is not locked
    /\ IF can_delete
        THEN do_delete_item(it)
        ELSE on_dec_only
    /\ UNCHANGED slab_lock

DeletePrevKey(n) ==
    LET
        k == local_key[n]
        it == hash_map[k]

        s == item_map[it].slab
    IN
    /\ pc[n] = "DeletePrevKey"
    /\ goto(n, "GetFreePage")

    /\ hash_map' = [hash_map EXCEPT ![k] = nil]
    /\ dec_refcount_or_delete(it, TRUE)

    /\ UNCHANGED free_pages
    /\ UNCHANGED hash_slot_lock
    /\ node_logic_unchanged

------------------------------------------------------------------

inc_lock_slab(s) ==
    /\ slab_lock' = [slab_lock EXCEPT ![s] = @ + 1]

clear_local_vars(n) ==
    /\ set_local(n, local_key, nil)
    /\ set_local(n, local_slab, nil)
    /\ set_local(n, local_item, nil)

do_unlock_hash_slot(n, h) ==
    /\ hash_slot_lock' = [hash_slot_lock EXCEPT ![h] = @ - 1]
    /\ goto(n, "Init")
    /\ clear_local_vars(n)
    /\ UNCHANGED const_vars
    /\ UNCHANGED stop_cmd

keep_locking_hash_slot ==
    /\ UNCHANGED hash_slot_lock
    /\ node_logic_unchanged

------------------------

GetFreePage(n) ==
    LET
        s == local_slab[n]
        k == local_key[n]
        h == key_to_slot[k]

        goto_set_item ==
            /\ goto(n, "SetItem")
            /\ inc_lock_slab(s)
            /\ UNCHANGED free_pages
            /\ UNCHANGED slab_free_items
            /\ keep_locking_hash_slot

        do_evict ==
            /\ goto(n, "EvictSlab")
            /\ inc_lock_slab(s)
            /\ UNCHANGED free_pages
            /\ UNCHANGED slab_free_items
            /\ keep_locking_hash_slot

        skip_put ==
            /\ do_unlock_hash_slot(n, h)
            /\ UNCHANGED slab_free_items
            /\ UNCHANGED free_pages
            /\ UNCHANGED slab_lock

        new_items(p) == {p} \X Offset

        on_alloc(p) ==
            /\ p \in free_pages
            /\ goto(n, "SetItem")
            /\ inc_lock_slab(s)
            /\ free_pages' = free_pages \ {p}
            /\ slab_free_items' = [slab_free_items EXCEPT ![s] = @ \union new_items(p)]
            /\ keep_locking_hash_slot

        do_action ==
            IF slab_free_items[s] # {} THEN
                goto_set_item
            ELSE IF free_pages # {} THEN
                \E p \in Page: on_alloc(p)
            ELSE IF slab_inuse_items[s] # {} THEN
                do_evict
            ELSE
                skip_put
    IN
    /\ pc[n] = "GetFreePage"

    /\ slab_lock[s] = 0
    /\ do_action

    /\ UNCHANGED slab_inuse_items
    /\ UNCHANGED <<item_map, hash_map>>

------------------------------------------------------------------

EvictSlab(n, it) ==
    LET
        s == local_slab[n]
        current_hash == key_to_slot[local_key[n]]

        k == item_map[it].key
        h == key_to_slot[k]

        try_lock_ok ==
            /\ current_hash # h => hash_slot_lock[h] = 0
            /\ item_map[it].refcount = 1
            /\ ~item_map[it].deleted

        on_normal ==
            /\ goto(n, "SetItem")
            /\ hash_map' = [hash_map EXCEPT ![k] = nil]
            /\ do_delete_item(it)
            /\ UNCHANGED slab_lock
            /\ keep_locking_hash_slot

        on_skip ==
            /\ slab_lock' = [slab_lock EXCEPT ![s] = @ - 1] \* unlock
            /\ do_unlock_hash_slot(n, current_hash)
            /\ UNCHANGED slab_free_items
            /\ UNCHANGED slab_inuse_items
            /\ UNCHANGED item_map
            /\ UNCHANGED hash_map
    IN
    /\ pc[n] = "EvictSlab"
    /\ it \in slab_inuse_items[s]

    /\ IF try_lock_ok
        THEN on_normal
        ELSE on_skip

    /\ UNCHANGED free_pages

------------------------------------------------------------------

SetItem(n, it) ==
    LET
        k == local_key[n]
        h == key_to_slot[k]
        s == local_slab[n]

        new_item == [
            key |-> k,
            slab |-> s,
            refcount |-> 1,
            deleted |-> FALSE
        ]
    IN
    /\ pc[n] = "SetItem"
    /\ it \in slab_free_items[s]

    /\ slab_free_items' = [slab_free_items EXCEPT ![s] = @ \ {it}]
    /\ slab_inuse_items' = [slab_inuse_items EXCEPT ![s] = @ \union {it}]
    /\ item_map' = [item_map EXCEPT ![it] = new_item]
    /\ hash_map' = [hash_map EXCEPT ![k] = it]
    /\ slab_lock' = [slab_lock EXCEPT ![s] = @ - 1]

    /\ do_unlock_hash_slot(n, h)

    /\ UNCHANGED free_pages

------------------------------------------------------------------

GetKey(n, k) ==
    LET
        h == key_to_slot[k]
        it == hash_map[k]
    IN
    /\ ~stop_cmd
    /\ pc[n] = "Init"
    /\ hash_slot_lock[h] = 0 \* do lock
    /\ it # nil

    /\ goto(n, "GetDecRef")
    /\ set_local(n, local_item, it)
    /\ item_map' = [item_map EXCEPT ![it].refcount = @ + 1]

    /\ UNCHANGED <<local_key, local_slab>>
    /\ UNCHANGED hash_slot_lock
    /\ UNCHANGED hash_map
    /\ UNCHANGED free_pages
    /\ UNCHANGED slab_vars
    /\ UNCHANGED const_vars
    /\ UNCHANGED stop_cmd

------------------------------------------------------------------

GetDecRef(n) ==
    LET
        it == local_item[n]
        k == item_map[it].key
        h == key_to_slot[k]
    IN
    /\ pc[n] = "GetDecRef"
    /\ hash_slot_lock[h] = 0 \* do lock

    /\ goto(n, "Init")
    /\ dec_refcount_or_delete(it, FALSE)
    /\ clear_local_vars(n)

    /\ UNCHANGED hash_map
    /\ UNCHANGED hash_slot_lock
    /\ UNCHANGED free_pages
    /\ UNCHANGED const_vars
    /\ UNCHANGED stop_cmd

------------------------------------------------------------------

DeleteKey(n, k) ==
    LET
        it == hash_map[k]
        h == key_to_slot[k]
    IN
    /\ ~stop_cmd
    /\ pc[n] = "Init"
    /\ hash_slot_lock[h] = 0 \* not locked
    /\ it # nil

    /\ hash_map' = [hash_map EXCEPT ![k] = nil]
    /\ dec_refcount_or_delete(it, TRUE)

    /\ UNCHANGED pc
    /\ UNCHANGED free_pages
    /\ UNCHANGED hash_slot_lock
    /\ node_logic_unchanged


------------------------------------------------------------------

EnableStopCmd ==
    /\ ~stop_cmd
    /\ stop_cmd' = TRUE

    /\ UNCHANGED <<hash_map, item_map, hash_slot_lock>>
    /\ UNCHANGED free_pages
    /\ UNCHANGED local_vars
    /\ UNCHANGED slab_vars
    /\ UNCHANGED const_vars

------------------------------------------------------------------

StopCond ==
    /\ \A n \in Node: pc[n] = "Init"

TerminateCond ==
    /\ StopCond
    /\ stop_cmd

Terminated ==
    /\ TerminateCond
    /\ UNCHANGED vars

------------------------------------------------------------------

Next ==
    \/ \E n \in Node, k \in Key, s \in Slab:
        \/ PutKey(n, k, s)
    \/ \E n \in Node:
        \/ LockSlot(n)
        \/ DeletePrevKey(n)
        \/ GetFreePage(n)
        \/ GetDecRef(n)
    \/ \E n \in Node, it \in Item:
        \/ EvictSlab(n, it)
        \/ SetItem(n, it)
    \/ \E n \in Node, k \in Key:
        \/ GetKey(n, k)
        \/ DeleteKey(n, k)
    \/ EnableStopCmd
    \/ Terminated

Spec == Init /\ [][Next]_vars

FairSpec == Spec /\ WF_vars(Next) /\ SF_vars(EnableStopCmd)

------------------------------------------------------------------

AlwaysTerminated == []<>TerminateCond

------------------------

NoLeakItem ==
    LET
        exist_key_of(it) == \E k \in Key: hash_map[k] = it

        cond ==
            \A it \in Item:
                item_map[it] # nil =>
                    /\ ~item_map[it].deleted
                    /\ item_map[it].refcount = 1
                    /\ exist_key_of(it)
    IN
        StopCond => cond

------------------------

HashMapNoDuplicate ==
    \A k1, k2 \in Key:
        LET
            pre_cond ==
                /\ k1 # k2
                /\ hash_map[k1] # nil
                /\ hash_map[k2] # nil

            cond ==
                /\ hash_map[k1] # hash_map[k2]
        IN
            pre_cond => cond

------------------------

SlabInuseItemsMatchItemMap ==
    LET
        exist_in_slab(it) ==
            \E s \in Slab: it \in slab_inuse_items[s]
    IN
    \A it \in Item:
        exist_in_slab(it) <=> item_map[it] # nil

------------------------

HashMapAlwaysPointToInuse ==
    LET
        exist_in_slab(it) ==
            \E s \in Slab: it \in slab_inuse_items[s]
    IN
    \A k \in Key:
        hash_map[k] # nil => exist_in_slab(hash_map[k])

------------------------

ItemAlwaysExistWhenSetItem ==
    \A n \in Node:
        LET
            s == local_slab[n]
            cond == slab_free_items[s] # {}
        IN
        pc[n] = "SetItem" => cond

------------------------

InitStateInv ==
    \A n \in Node:
        pc[n] = "Init" =>
            /\ local_key[n] = nil
            /\ local_slab[n] = nil
            /\ local_item[n] = nil

------------------------

GetDecRefItemAlwaysExist ==
    \A n \in Node:
        LET
            it == local_item[n]
        IN
        pc[n] = "GetDecRef" => item_map[it] # nil

------------------------

StopCondInv ==
    LET
        cond ==
            /\ \A s \in Slab: slab_lock[s] = 0
            /\ \A h \in HashSlot: hash_slot_lock[h] = 0
    IN
    StopCond => cond

------------------------

MutexLockCond ==
    /\ \A h \in HashSlot: hash_slot_lock[h] \in 0..1
    /\ \A s \in Slab: slab_lock[s] \in 0..1

\* TODO add avoid race condition for hash slot

====

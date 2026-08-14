---- MODULE Memcached ----
EXTENDS TLC, Naturals, FiniteSets

CONSTANTS Node, Key, HashSlot, Page, Offset, Slab, nil

VARIABLES
    key_to_hash_slot,
    pc, local_key, local_slab, local_item,
    free_pages, hash_slot_lock,
    slab_lock, slab_pages,
    slab_free_items, slab_inuse_items,
    mover_need_delete,
    item_map, hash_map,
    move_pc, move_from_slab,
    move_local_page, move_items, slab_move_page,
    stop_cmd

const_vars == <<
    key_to_hash_slot
>>

local_vars == <<
    pc, local_key, local_slab, local_item
>>

slab_vars == <<
    slab_lock, slab_pages,
    slab_free_items, slab_inuse_items,
    mover_need_delete
>>

move_vars == <<
    move_pc, move_from_slab,
    move_local_page, move_items, slab_move_page
>>

vars == <<
    const_vars,
    local_vars,
    free_pages, hash_slot_lock,
    slab_vars,
    item_map, hash_map,
    move_vars,
    stop_cmd
>>

------------------------------------------------------------------

is_disjoint(S1, S2) ==
    S1 \intersect S2 = {}

------------------------------------------------------------------

Null(S) == S \union {nil}

Item == Page \X Offset

ItemData == [
    key: Key,
    slab: Slab,
    refcount: Nat,
    partial_set: BOOLEAN
]

PC == {
    "Init", "LockSlot",
    "DeletePrevKey", "GetFreePage",
    "EvictSlab", "SetItem", "FinishSetItem",
    "GetDecRef"
}

MovePC == {"Init", "MoverDeleteItem", "MoverRemovePage", "MoverFinish"}

ItemHashSlot == [
    item: Item,
    hash: HashSlot
]

------------------------------------------------------------------

TypeOK ==
    /\ key_to_hash_slot \in [Key -> HashSlot]
    /\ free_pages \subseteq Page
    /\ hash_slot_lock \in [HashSlot -> Nat]

    /\ slab_lock \in [Slab -> Nat]
    /\ slab_pages \in [Slab -> SUBSET Page]
    /\ slab_free_items \in [Slab -> SUBSET Item]
    /\ slab_inuse_items \in [Slab -> SUBSET Item]
    /\ mover_need_delete \in Null(Nat)

    /\ item_map \in [Item -> Null(ItemData)]
    /\ hash_map \in [Key -> Null(Item)]

    /\ pc \in [Node -> PC]
    /\ local_key \in [Node -> Null(Key)]
    /\ local_slab \in [Node -> Null(Slab)]
    /\ local_item \in [Node -> Null(Item)]

    /\ move_pc \in MovePC
    /\ move_from_slab \in Null(Slab)
    /\ move_local_page \in Null(Page)
    /\ move_items \subseteq ItemHashSlot
    /\ slab_move_page \in [Slab -> Null(Page)]

    /\ stop_cmd \in BOOLEAN

Init ==
    /\ key_to_hash_slot \in [Key -> HashSlot]
    /\ free_pages = Page
    /\ hash_slot_lock = [h \in HashSlot |-> 0]

    /\ slab_lock = [s \in Slab |-> 0]
    /\ slab_pages = [s \in Slab |-> {}]
    /\ slab_free_items = [s \in Slab |-> {}]
    /\ slab_inuse_items = [s \in Slab |-> {}]
    /\ mover_need_delete = nil

    /\ item_map = [i \in Item |-> nil]
    /\ hash_map = [k \in Key |-> nil]

    /\ pc = [n \in Node |-> "Init"]
    /\ local_key = [n \in Node |-> nil]
    /\ local_slab = [n \in Node |-> nil]
    /\ local_item = [n \in Node |-> nil]

    /\ move_pc = "Init"
    /\ move_from_slab = nil
    /\ move_local_page = nil
    /\ move_items = {}
    /\ slab_move_page = [s \in Slab |-> nil]

    /\ stop_cmd = FALSE

------------------------------------------------------------------

set_local(n, var, x) ==
    var' = [var EXCEPT ![n] = x]

goto(n, l) ==
    pc' = [pc EXCEPT ![n] = l]

node_base_unchanged ==
    /\ UNCHANGED const_vars
    /\ UNCHANGED move_vars
    /\ UNCHANGED stop_cmd

node_logic_unchanged ==
    /\ UNCHANGED <<local_key, local_slab, local_item>>
    /\ node_base_unchanged

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
    /\ node_base_unchanged

------------------------------------------------------------------

do_lock_hash_slot(h) ==
    /\ hash_slot_lock[h] = 0
    /\ hash_slot_lock' = [hash_slot_lock EXCEPT ![h] = @ + 1]

------------------------

LockSlot(n) ==
    LET
        k == local_key[n]
        h == key_to_hash_slot[k]

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
        p == it[1]

        is_moving ==
            slab_move_page[s] = p

        when_normal ==
            /\ slab_free_items' = [slab_free_items EXCEPT ![s] = @ \union {it}]
            /\ UNCHANGED mover_need_delete

        when_moving ==
            /\ mover_need_delete' = mover_need_delete - 1
            /\ UNCHANGED slab_free_items
    IN
    /\ item_map' = [item_map EXCEPT ![it] = nil]
    /\ IF is_moving
        THEN when_moving
        ELSE when_normal
    /\ slab_inuse_items' = [slab_inuse_items EXCEPT ![s] = @ \ {it}]

do_delete_item_unchanged ==
    /\ UNCHANGED item_map
    /\ UNCHANGED mover_need_delete
    /\ UNCHANGED <<slab_free_items, slab_inuse_items>>

------------------------

dec_refcount_or_delete(it, clear_partial) ==
    LET
        k == item_map[it].key
        s == item_map[it].slab

        can_delete ==
            item_map[it].refcount = 1

        on_dec_only ==
            /\ item_map' = [item_map EXCEPT
                    ![it].refcount = @ - 1,
                    ![it].partial_set = @ /\ ~clear_partial
                ]
            /\ UNCHANGED slab_free_items
            /\ UNCHANGED slab_inuse_items
            /\ UNCHANGED mover_need_delete
    IN
    /\ slab_lock[s] = 0 \* slab is not locked
    /\ IF can_delete
        THEN do_delete_item(it)
        ELSE on_dec_only
    /\ UNCHANGED slab_lock
    /\ UNCHANGED slab_pages

dec_refcount_unchanged ==
    /\ do_delete_item_unchanged
    /\ UNCHANGED slab_lock
    /\ UNCHANGED slab_pages

normal_dec_refcount_or_delete(it) ==
    dec_refcount_or_delete(it, FALSE)

------------------------------------------------------------------

DeletePrevKey(n) ==
    LET
        k == local_key[n]
        it == hash_map[k]

        s == item_map[it].slab
    IN
    /\ pc[n] = "DeletePrevKey"
    /\ goto(n, "GetFreePage")

    /\ hash_map' = [hash_map EXCEPT ![k] = nil]
    /\ normal_dec_refcount_or_delete(it)

    /\ UNCHANGED free_pages
    /\ UNCHANGED hash_slot_lock
    /\ node_logic_unchanged

------------------------------------------------------------------

inc_slab_lock(s) ==
    /\ slab_lock' = [slab_lock EXCEPT ![s] = @ + 1]

dec_slab_lock(s) ==
    /\ slab_lock' = [slab_lock EXCEPT ![s] = @ - 1]

clear_local_vars(n) ==
    /\ set_local(n, local_key, nil)
    /\ set_local(n, local_slab, nil)
    /\ set_local(n, local_item, nil)

dec_hash_slot_lock(h) ==
    /\ hash_slot_lock' = [hash_slot_lock EXCEPT ![h] = @ - 1]

do_unlock_hash_slot(n, h) ==
    /\ dec_hash_slot_lock(h)
    /\ goto(n, "Init")
    /\ clear_local_vars(n)
    /\ node_base_unchanged

keep_locking_hash_slot ==
    /\ UNCHANGED hash_slot_lock
    /\ node_logic_unchanged

------------------------

GetFreePage(n) ==
    LET
        s == local_slab[n]
        k == local_key[n]
        h == key_to_hash_slot[k]

        slab_unchanged ==
            /\ UNCHANGED free_pages
            /\ UNCHANGED slab_free_items
            /\ UNCHANGED slab_pages

        goto_set_item ==
            /\ goto(n, "SetItem")
            /\ inc_slab_lock(s)
            /\ keep_locking_hash_slot
            /\ slab_unchanged

        do_evict ==
            /\ goto(n, "EvictSlab")
            /\ inc_slab_lock(s)
            /\ keep_locking_hash_slot
            /\ slab_unchanged

        skip_put ==
            /\ do_unlock_hash_slot(n, h)
            /\ UNCHANGED slab_lock
            /\ slab_unchanged

        new_items(p) == {p} \X Offset

        on_alloc(p) ==
            /\ p \in free_pages
            /\ goto(n, "SetItem")
            /\ inc_slab_lock(s)
            /\ free_pages' = free_pages \ {p}
            /\ slab_pages' = [slab_pages EXCEPT ![s] = @ \union {p}]
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
    /\ UNCHANGED mover_need_delete
    /\ UNCHANGED <<item_map, hash_map>>

------------------------------------------------------------------

EvictSlab(n, it) ==
    LET
        s == local_slab[n]
        current_hash == key_to_hash_slot[local_key[n]]

        k == item_map[it].key
        h == key_to_hash_slot[k]

        try_lock_ok ==
            /\ current_hash # h => hash_slot_lock[h] = 0
            /\ item_map[it].refcount = 1
            /\ hash_map[k] = it \* not deleted
            /\ slab_move_page[s] # it[1] \* page is not moving

        on_normal ==
            /\ goto(n, "SetItem")
            /\ hash_map' = [hash_map EXCEPT ![k] = nil]
            /\ do_delete_item(it)
            /\ UNCHANGED slab_lock
            /\ keep_locking_hash_slot
            /\ UNCHANGED slab_pages

        on_skip ==
            /\ dec_slab_lock(s)
            /\ do_unlock_hash_slot(n, current_hash)
            /\ do_delete_item_unchanged
            /\ UNCHANGED slab_pages
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
        h == key_to_hash_slot[k]
        s == local_slab[n]

        new_item == [
            key |-> k,
            slab |-> s,
            refcount |-> 1,
            partial_set |-> FALSE
        ]

        fully_set ==
            /\ item_map' = [item_map EXCEPT ![it] = new_item]
            /\ do_unlock_hash_slot(n, h)

        partial_item == [new_item EXCEPT
            !.partial_set = TRUE,
            !.refcount = @ + 1
        ]

        partial_set ==
            /\ goto(n, "FinishSetItem")
            /\ item_map' = [item_map EXCEPT ![it] = partial_item]
            /\ dec_hash_slot_lock(h)
            /\ set_local(n, local_item, it)

            /\ UNCHANGED <<local_key, local_slab>>
            /\ node_base_unchanged
    IN
    /\ pc[n] = "SetItem"
    /\ it \in slab_free_items[s]

    /\ slab_free_items' = [slab_free_items EXCEPT ![s] = @ \ {it}]
    /\ slab_inuse_items' = [slab_inuse_items EXCEPT ![s] = @ \union {it}]
    /\ hash_map' = [hash_map EXCEPT ![k] = it]
    /\ dec_slab_lock(s)
    /\ \/ fully_set
       \/ partial_set

    /\ UNCHANGED mover_need_delete
    /\ UNCHANGED slab_pages
    /\ UNCHANGED free_pages

------------------------------------------------------------------

with_single_atomic_step(h) ==
    /\ hash_slot_lock[h] = 0 \* do lock
    /\ UNCHANGED hash_slot_lock
    /\ UNCHANGED free_pages
    /\ node_base_unchanged

FinishSetItem(n) ==
    LET
        k == local_key[n]
        h == key_to_hash_slot[k]
        it == local_item[n]
    IN
    /\ pc[n] = "FinishSetItem"
    /\ with_single_atomic_step(h)

    /\ goto(n, "Init")
    /\ dec_refcount_or_delete(it, TRUE)
    /\ clear_local_vars(n)

    /\ UNCHANGED hash_map

------------------------------------------------------------------

GetKey(n, k) ==
    LET
        h == key_to_hash_slot[k]
        it == hash_map[k]
    IN
    /\ ~stop_cmd
    /\ pc[n] = "Init"
    /\ it # nil
    /\ with_single_atomic_step(h)
    /\ ~item_map[it].partial_set

    /\ goto(n, "GetDecRef")
    /\ set_local(n, local_item, it)
    /\ item_map' = [item_map EXCEPT ![it].refcount = @ + 1]

    /\ UNCHANGED <<local_key, local_slab>>
    /\ UNCHANGED hash_map
    /\ UNCHANGED slab_vars

------------------------------------------------------------------

\* Finish Get
GetDecRef(n) ==
    LET
        it == local_item[n]
        k == item_map[it].key
        h == key_to_hash_slot[k]
    IN
    /\ pc[n] = "GetDecRef"
    /\ with_single_atomic_step(h)

    /\ goto(n, "Init")
    /\ dec_refcount_or_delete(it, FALSE)
    /\ clear_local_vars(n)

    /\ UNCHANGED hash_map

------------------------------------------------------------------

DeleteKey(n, k) ==
    LET
        it == hash_map[k]
        h == key_to_hash_slot[k]
    IN
    /\ ~stop_cmd
    /\ pc[n] = "Init"
    /\ hash_slot_lock[h] = 0 \* not locked
    /\ it # nil

    /\ hash_map' = [hash_map EXCEPT ![k] = nil]
    /\ normal_dec_refcount_or_delete(it)

    /\ UNCHANGED pc
    /\ UNCHANGED free_pages
    /\ UNCHANGED hash_slot_lock
    /\ node_logic_unchanged


------------------------------------------------------------------

mover_unchanged ==
    /\ UNCHANGED local_vars
    /\ UNCHANGED const_vars
    /\ UNCHANGED stop_cmd

StartMovePage(s, p) ==
    LET
        remove_items == {p} \X Offset

        inuse ==
            {it \in slab_inuse_items[s]: it[1] = p}

        single_move_item(it) == [
            item |-> it,
            hash |-> key_to_hash_slot[item_map[it].key]
        ]

        new_move_items == {single_move_item(it): it \in inuse}
    IN
    /\ ~stop_cmd
    /\ move_pc = "Init"
    /\ slab_lock[s] = 0 \* lock slab
    /\ p \in slab_pages[s]

    /\ move_pc' = "MoverDeleteItem"
    /\ move_from_slab' = s
    /\ move_local_page' = p
    /\ move_items' = new_move_items

    /\ slab_free_items' = [slab_free_items EXCEPT ![s] = @ \ remove_items]
    /\ slab_move_page' = [slab_move_page EXCEPT ![s] = p]
    /\ mover_need_delete' = Cardinality(inuse)

    /\ UNCHANGED slab_lock
    /\ UNCHANGED <<slab_pages, slab_inuse_items>>
    /\ UNCHANGED <<free_pages, hash_map, hash_slot_lock, item_map>>

    /\ mover_unchanged

------------------------------------------------------------------

mover_on_delete(it_hash) ==
    LET
        it == it_hash.item
        h == it_hash.hash
        s == move_from_slab
        k == item_map[it].key

        can_delete ==
            /\ item_map[it] # nil
            /\ hash_map[k] = it \* not deleted

        on_delete_nop ==
            /\ dec_refcount_unchanged
            /\ UNCHANGED hash_map

        on_delete_normal ==
            /\ dec_refcount_or_delete(it, FALSE)
            /\ hash_map' = [hash_map EXCEPT ![k] = nil]
    IN
    /\ hash_slot_lock[h] = 0 \* lock slot
    /\ slab_lock[s] = 0 \* lock slab

    /\ IF can_delete
        THEN on_delete_normal
        ELSE on_delete_nop

    /\ move_items' = move_items \ {it_hash}

    /\ UNCHANGED move_pc
    /\ UNCHANGED slab_lock

MoverDeleteItem ==
    LET
        s == move_from_slab

        on_finish ==
            /\ move_pc' = "MoverRemovePage"
            /\ UNCHANGED <<hash_map, item_map>>
            /\ UNCHANGED slab_vars
            /\ UNCHANGED move_items
    IN
    /\ move_pc = "MoverDeleteItem"

    /\ IF move_items = {}
        THEN on_finish
        ELSE \E it_hash \in move_items: mover_on_delete(it_hash)

    /\ UNCHANGED hash_slot_lock
    /\ UNCHANGED <<move_from_slab, move_local_page>>
    /\ UNCHANGED <<free_pages, slab_pages, slab_move_page>>
    /\ mover_unchanged

------------------------------------------------------------------

MoverRemovePage ==
    LET
        s == move_from_slab
        p == move_local_page
    IN
    /\ move_pc = "MoverRemovePage"
    /\ slab_lock[s] = 0 \* lock slab
    /\ mover_need_delete = 0 \* wait until delete count = 0

    /\ move_pc' = "MoverFinish"
    /\ mover_need_delete' = nil
    /\ slab_move_page' = [slab_move_page EXCEPT ![s] = nil]
    /\ slab_pages' = [slab_pages EXCEPT ![s] = @ \ {p}]

    /\ UNCHANGED <<hash_slot_lock, hash_map, item_map>>
    /\ UNCHANGED <<slab_lock, slab_free_items, slab_inuse_items>>
    /\ UNCHANGED <<move_from_slab, move_local_page>>
    /\ UNCHANGED move_items
    /\ UNCHANGED free_pages
    /\ mover_unchanged

------------------------------------------------------------------

MoverFinish(s) ==
    LET
        p == move_local_page
        new_items == {p} \X Offset
    IN
    /\ move_pc = "MoverFinish"
    /\ s # move_from_slab
    /\ slab_lock[s] = 0 \* lock slab

    /\ slab_pages' = [slab_pages EXCEPT ![s] = @ \union {p}]
    /\ slab_free_items' = [slab_free_items EXCEPT ![s] = @ \union new_items]

    /\ mover_need_delete' = nil
    /\ move_pc' = "Init"
    /\ move_from_slab' = nil
    /\ move_local_page' = nil

    /\ UNCHANGED move_items
    /\ UNCHANGED slab_move_page
    /\ UNCHANGED <<hash_map, item_map, hash_slot_lock>>
    /\ UNCHANGED free_pages
    /\ UNCHANGED <<slab_lock, slab_inuse_items>>
    /\ mover_unchanged

------------------------------------------------------------------

EnableStopCmd ==
    /\ ~stop_cmd
    /\ stop_cmd' = TRUE

    /\ UNCHANGED <<hash_map, item_map, hash_slot_lock>>
    /\ UNCHANGED free_pages
    /\ UNCHANGED local_vars
    /\ UNCHANGED slab_vars
    /\ UNCHANGED const_vars
    /\ UNCHANGED move_vars

------------------------------------------------------------------

StopCond ==
    /\ \A n \in Node: pc[n] = "Init"
    /\ move_pc = "Init"

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
        \/ FinishSetItem(n)
        \/ GetFreePage(n)
        \/ GetDecRef(n)
    \/ \E n \in Node, it \in Item:
        \/ EvictSlab(n, it)
        \/ SetItem(n, it)
    \/ \E n \in Node, k \in Key:
        \/ GetKey(n, k)
        \/ DeleteKey(n, k)
    \/ \E s \in Slab, p \in Page:
        \/ StartMovePage(s, p)
    \/ MoverDeleteItem
    \/ MoverRemovePage
    \/ \E s \in Slab:
        \/ MoverFinish(s)
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

        item_cond(it) ==
            /\ ~item_map[it].partial_set
            /\ item_map[it].refcount = 1
            /\ exist_key_of(it)

        cond ==
            \A it \in Item:
                item_map[it] # nil => item_cond(it)
    IN
        StopCond => cond

------------------------

HashMapAlwaysPointToNonDeleted ==
    \A k \in Key:
        LET it == hash_map[k] IN
        it # nil => item_map[it].refcount > 0

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
        pc[n] = "GetDecRef" =>
            /\ item_map[it] # nil
            /\ item_map[it].partial_set = FALSE

------------------------

FinishSetItemPartialAlwaysTrue ==
    \A n \in Node:
        LET
            it == local_item[n]

            cond ==
                /\ item_map[it] # nil
                /\ item_map[it].partial_set
        IN
        pc[n] = "FinishSetItem" => cond

------------------------

PageAllocInv ==
    LET
        exist_page_in_slab(p) ==
            \E s \in Slab: p \in slab_pages[s]

        cond(p) ==
            ~exist_page_in_slab(p) <=> p \in free_pages
    IN
        \A p \in Page: move_pc = "Init" => cond(p)

------------------------

SlabPagesDisjoint ==
    \A s1, s2 \in Slab:
        s1 # s2 => is_disjoint(slab_pages[s1], slab_pages[s2])

------------------------

SlabPagesInv ==
    LET
        slab_item_set(s) ==
            slab_inuse_items[s] \union slab_free_items[s]

        slab_page_items(s) ==
            slab_pages[s] \X Offset
    IN
    \A s \in Slab:
        /\ move_pc = "Init" => slab_item_set(s) = slab_page_items(s)
        /\ is_disjoint(slab_inuse_items[s], slab_free_items[s])

------------------------

SlabMovePageInv ==
    \A s \in Slab:
        LET
            cond ==
                /\ move_from_slab = s
                /\ move_local_page = slab_move_page[s]
        IN
            /\ slab_move_page[s] # nil <=> cond
            /\ slab_move_page[s] # nil =>
                    slab_move_page[s] \in slab_pages[s]

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

====

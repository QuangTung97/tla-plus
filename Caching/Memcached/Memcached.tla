---- MODULE Memcached ----
EXTENDS TLC, Naturals

CONSTANTS Node, Key, HashSlot, Page, Offset, Slab, nil

VARIABLES
    key_to_slot,
    pc, local_key, local_slab,
    free_pages, hash_slot_lock,
    slab_free_items, slab_inuse_items,
    item_map, hash_map

const_vars == <<
    key_to_slot
>>

local_vars == <<
    pc, local_key, local_slab
>>

slab_vars == <<
    slab_free_items, slab_inuse_items
>>

vars == <<
    const_vars,
    local_vars,
    free_pages, hash_slot_lock,
    slab_vars,
    item_map, hash_map
>>

------------------------------------------------------------------

Null(S) == S \union {nil}

Item == Page \X Offset

ItemData == [
    key: Key
]

PC == {"Init", "LockSlot", "GetFreePage", "SetItem", "UnlockSlot"}

------------------------------------------------------------------

TypeOK ==
    /\ key_to_slot \in [Key -> HashSlot]
    /\ free_pages \subseteq Page
    /\ hash_slot_lock \in [HashSlot -> Nat]

    /\ slab_free_items \in [Slab -> SUBSET Item]
    /\ slab_inuse_items \in [Slab -> SUBSET Item]
    /\ item_map \in [Item -> Null(ItemData)]
    /\ hash_map \in [Key -> Null(Item)]

    /\ pc \in [Node -> PC]
    /\ local_key \in [Node -> Null(Key)]
    /\ local_slab \in [Node -> Null(Slab)]

Init ==
    /\ key_to_slot \in [Key -> HashSlot]
    /\ free_pages = Page
    /\ hash_slot_lock = [h \in HashSlot |-> 0]

    /\ slab_free_items = [s \in Slab |-> {}]
    /\ slab_inuse_items = [s \in Slab |-> {}]
    /\ item_map = [i \in Item |-> nil]
    /\ hash_map = [k \in Key |-> nil]

    /\ pc = [n \in Node |-> "Init"]
    /\ local_key = [n \in Node |-> nil]
    /\ local_slab = [n \in Node |-> nil]

------------------------------------------------------------------

set_local(n, var, x) ==
    var' = [var EXCEPT ![n] = x]

goto(n, l) ==
    pc' = [pc EXCEPT ![n] = l]

node_logic_unchanged ==
    /\ UNCHANGED const_vars
    /\ UNCHANGED <<local_key, local_slab>>

------------------------------------------------------------------

PutKey(n, k, s) ==
    /\ pc[n] = "Init"
    /\ goto(n, "LockSlot")
    /\ set_local(n, local_key, k)
    /\ set_local(n, local_slab, s)

    /\ UNCHANGED <<free_pages, hash_slot_lock>>
    /\ UNCHANGED slab_vars
    /\ UNCHANGED <<item_map, hash_map>>
    /\ UNCHANGED const_vars

------------------------------------------------------------------

do_lock_hash_slot(h) ==
    /\ hash_slot_lock[h] = 0
    /\ hash_slot_lock' = [hash_slot_lock EXCEPT ![h] = @ + 1]

LockSlot(n) ==
    LET
        k == local_key[n]
        h == key_to_slot[k]
    IN
    /\ pc[n] = "LockSlot"

    /\ do_lock_hash_slot(h)
    /\ goto(n, "GetFreePage")

    /\ UNCHANGED free_pages
    /\ UNCHANGED slab_vars
    /\ UNCHANGED <<item_map, hash_map>>
    /\ node_logic_unchanged

------------------------------------------------------------------

GetFreePage(n, p) ==
    LET
        s == local_slab[n]
        new_items == {p} \X Offset
    IN
    /\ p \in free_pages
    /\ pc[n] = "GetFreePage"

    /\ goto(n, "SetItem")
    /\ free_pages' = free_pages \ {p}
    /\ slab_free_items' = [slab_free_items EXCEPT ![s] = @ \union new_items]

    /\ UNCHANGED slab_inuse_items
    /\ UNCHANGED <<item_map, hash_map>>
    /\ UNCHANGED hash_slot_lock
    /\ node_logic_unchanged

------------------------------------------------------------------

SetItem(n, it) ==
    LET
        k == local_key[n]
        s == local_slab[n]

        new_item == [
            key |-> k
        ]
    IN
    /\ pc[n] = "SetItem"
    /\ it \in slab_free_items[s]

    /\ goto(n, "UnlockSlot")
    /\ slab_free_items' = [slab_free_items EXCEPT ![s] = @ \ {it}]
    /\ slab_inuse_items' = [slab_inuse_items EXCEPT ![s] = @ \union {it}]
    /\ item_map' = [item_map EXCEPT ![it] = new_item]
    /\ hash_map' = [hash_map EXCEPT ![k] = it]

    /\ UNCHANGED hash_slot_lock
    /\ UNCHANGED free_pages
    /\ node_logic_unchanged

------------------------------------------------------------------

UnlockSlot(n) ==
    LET
        k == local_key[n]
        h == key_to_slot[k]
    IN
    /\ pc[n] = "UnlockSlot"
    /\ goto(n, "Init")
    /\ hash_slot_lock' = [hash_slot_lock EXCEPT ![h] = @ - 1]

    /\ UNCHANGED <<item_map, hash_map>>
    /\ UNCHANGED slab_vars
    /\ UNCHANGED free_pages
    /\ node_logic_unchanged

------------------------------------------------------------------

StopCond ==
    /\ \A n \in Node: pc[n] = "Init"

Terminated ==
    /\ StopCond
    /\ UNCHANGED vars

------------------------------------------------------------------

Next ==
    \/ \E n \in Node, k \in Key, s \in Slab:
        \/ PutKey(n, k, s)
    \/ \E n \in Node:
        \/ LockSlot(n)
        \/ UnlockSlot(n)
    \/ \E n \in Node, p \in Page:
        \/ GetFreePage(n, p)
    \/ \E n \in Node, it \in Item:
        \/ SetItem(n, it)
    \/ Terminated

Spec == Init /\ [][Next]_vars

------------------------------------------------------------------

NoLeakItem ==
    LET
        exist_key_of(it) == \E k \in Key: hash_map[k] = it

        cond ==
            \A it \in Item:
                item_map[it] # nil => exist_key_of(it)
    IN
    StopCond => cond

====

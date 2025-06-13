----- MODULE SlabCache ----
EXTENDS TLC, Naturals, Sequences

CONSTANTS Node, Slot, nil, max_val

VARIABLES
    table, table_lock, global_mem, next_val,
    pc, local_addr, local_del_addr

vars == <<
    table, table_lock, global_mem, next_val,
    pc, local_addr, local_del_addr
>>

---------------------------------------------------------------------

Value == 20..29

Addr == DOMAIN global_mem

NullAddr == Addr \union {nil}

SlabItem == [
    ref: 0..10,
    slot: Slot,
    val: Value,
    freed: {0, 1}
]

PC == {
    "Init", "SetItemUnlock", "DeleteItem",
    "GetUnlockItem", "ReadValue",
    "Terminated"
}

---------------------------------------------------------------------

TypeOK ==
    /\ table \in [Slot -> NullAddr]
    /\ table_lock \in [Slot -> {"NoLock", "Locked"}]
    /\ global_mem \in Seq(SlabItem)
    /\ next_val \in Value

    /\ pc \in [Node -> PC]
    /\ local_addr \in [Node -> NullAddr]
    /\ local_del_addr \in [Node -> NullAddr]


Init ==
    /\ table = [s \in Slot |-> nil]
    /\ table_lock = [s \in Slot |-> "NoLock"]
    /\ global_mem = <<>>
    /\ next_val = 20

    /\ pc = [n \in Node |-> "Init"]
    /\ local_addr = [n \in Node |-> nil]
    /\ local_del_addr = [n \in Node |-> nil]

---------------------------------------------------------------------

goto(n, l) ==
    /\ pc' = [pc EXCEPT ![n] = l]

lock_slot(s) ==
    /\ table_lock[s] = "NoLock"
    /\ table_lock' = [table_lock EXCEPT ![s] = "Locked"]

unlock_slot(s) ==
    /\ table_lock' = [table_lock EXCEPT ![s] = "NoLock"]

inc_next_val ==
    /\ next_val < 20 + max_val
    /\ next_val' = next_val + 1


SetNewItem(n, s) ==
    LET
        new_obj == [
            ref |-> 1,
            slot |-> s,
            val |-> next_val',
            freed |-> 0
        ]

        addr == Len(global_mem')

        when_set_new ==
            /\ goto(n, "SetItemUnlock")
            /\ global_mem' = Append(global_mem, new_obj)
            /\ local_addr' = [local_addr EXCEPT ![n] = addr]
            /\ table' = [table EXCEPT ![s] = addr]
            /\ UNCHANGED local_del_addr

        old_addr == table[s]

        dec_ref ==
            [global_mem EXCEPT ![old_addr].ref = @ - 1]

        when_update ==
            /\ goto(n, "SetItemUnlock")
            /\ global_mem' = Append(dec_ref, new_obj)
            /\ local_addr' = [local_addr EXCEPT ![n] = addr]
            /\ table' = [table EXCEPT ![s] = addr]

            /\ IF global_mem'[old_addr].ref = 0
                THEN local_del_addr' = [local_del_addr EXCEPT ![n] = old_addr]
                ELSE UNCHANGED local_del_addr
    IN
    /\ pc[n] = "Init"
    /\ lock_slot(s)
    /\ inc_next_val
    /\ IF table[s] = nil
        THEN when_set_new
        ELSE when_update


SetItemUnlock(n) ==
    LET
        addr == local_addr[n]
        obj == global_mem[addr]
        s == obj.slot

        without_del ==
            /\ goto(n, "Terminated")
            /\ UNCHANGED local_del_addr

        with_del ==
            /\ goto(n, "DeleteItem")
            /\ UNCHANGED local_del_addr
    IN
    /\ pc[n] = "SetItemUnlock"
    /\ local_addr' = [local_addr EXCEPT ![n] = nil]
    /\ unlock_slot(s)

    /\ IF local_del_addr[n] # nil
        THEN with_del
        ELSE without_del

    /\ UNCHANGED next_val
    /\ UNCHANGED global_mem
    /\ UNCHANGED table


DeleteItem(n) ==
    LET
        addr == local_del_addr[n]
    IN
    /\ pc[n] = "DeleteItem"
    /\ goto(n, "Terminated")

    /\ global_mem' = [global_mem EXCEPT ![addr].freed = @ + 1]
    /\ local_del_addr' = [local_del_addr EXCEPT ![n] = nil]

    /\ UNCHANGED local_addr
    /\ UNCHANGED next_val
    /\ UNCHANGED <<table, table_lock>>


GetItem(n, s) ==
    /\ pc[n] = "Init"
    /\ lock_slot(s)
    /\ table[s] # nil
    /\ goto(n, "GetUnlockItem")

    /\ local_addr' = [local_addr EXCEPT ![n] = table[s]]
    /\ global_mem' = [global_mem EXCEPT ![table[s]].ref = @ + 1]

    /\ UNCHANGED local_del_addr
    /\ UNCHANGED next_val
    /\ UNCHANGED table


GetUnlockItem(n) ==
    LET
        addr == local_addr[n]
        s == global_mem[addr].slot
    IN
    /\ pc[n] = "GetUnlockItem"
    /\ goto(n, "ReadValue")
    /\ unlock_slot(s)

    /\ UNCHANGED local_addr
    /\ UNCHANGED global_mem
    /\ UNCHANGED local_del_addr
    /\ UNCHANGED next_val
    /\ UNCHANGED table


ReadValue(n) ==
    LET
        addr == local_addr[n]
        s == global_mem[addr].slot
    IN
    /\ pc[n] = "ReadValue"
    /\ goto(n, "Terminated")

    /\ local_addr' = [local_addr EXCEPT ![n] = nil]
    /\ UNCHANGED global_mem

    /\ UNCHANGED local_del_addr
    /\ UNCHANGED next_val
    /\ UNCHANGED <<table, table_lock>>

---------------------------------------------------------------------

TerminateCond ==
    /\ \A n \in Node: pc[n] = "Terminated"

Terminated ==
    /\ TerminateCond
    /\ UNCHANGED vars


Next ==
    \/ \E n \in Node, s \in Slot:
        \/ SetNewItem(n, s)
        \/ GetItem(n, s)
    \/ \E n \in Node:
        \/ SetItemUnlock(n)
        \/ DeleteItem(n)
        \/ GetUnlockItem(n)
        \/ ReadValue(n)
    \/ Terminated

Spec == Init /\ [][Next]_vars

---------------------------------------------------------------------

itemActiveOrFreeCondition ==
    \A addr \in DOMAIN global_mem:
        LET
            obj == global_mem[addr]
            when_not_free ==
                /\ obj.ref > 0
                /\ \E s \in Slot: table[s] = addr
        IN
            \/ obj.ref = 0
            \/ /\ obj.ref > 0
               /\ when_not_free

ItemActiveOrFreeInv ==
    TerminateCond => itemActiveOrFreeCondition


MustBeFreedWhenRefZero ==
    TerminateCond =>
        \A addr \in DOMAIN global_mem:
            LET
                obj == global_mem[addr]
            IN
                obj.ref = 0 => obj.freed = 1


CanNotReadFreedItem ==
    \A n \in Node:
        LET
            addr == local_addr[n]
            obj == global_mem[addr]
        IN
            ENABLED ReadValue(n) => obj.freed = 0

====

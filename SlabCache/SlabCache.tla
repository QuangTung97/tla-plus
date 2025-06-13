----- MODULE SlabCache ----
EXTENDS TLC, Naturals, Sequences

CONSTANTS Node, Slot, nil, max_val

VARIABLES
    table, table_lock, global_mem, next_val,
    pc, local_addr

vars == <<
    table, table_lock, global_mem, next_val,
    pc, local_addr
>>

---------------------------------------------------------------------

Value == 20..29

Addr == DOMAIN global_mem

NullAddr == Addr \union {nil}

SlabItem == [
    ref: 0..10,
    slot: Slot,
    val: Value
]

PC == {"Init", "SetItemUnlock", "Terminated"}

---------------------------------------------------------------------

TypeOK ==
    /\ table \in [Slot -> NullAddr]
    /\ table_lock \in [Slot -> {"NoLock", "Locked"}]
    /\ global_mem \in Seq(SlabItem)
    /\ next_val \in Value

    /\ pc \in [Node -> PC]
    /\ local_addr \in [Node -> NullAddr]


Init ==
    /\ table = [s \in Slot |-> nil]
    /\ table_lock = [s \in Slot |-> "NoLock"]
    /\ global_mem = <<>>
    /\ next_val = 20

    /\ pc = [n \in Node |-> "Init"]
    /\ local_addr = [n \in Node |-> nil]

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
            val |-> next_val'
        ]

        addr == Len(global_mem')
    IN
    /\ pc[n] = "Init"
    /\ lock_slot(s)

    /\ inc_next_val
    /\ goto(n, "SetItemUnlock")

    /\ global_mem' = Append(global_mem, new_obj)
    /\ local_addr' = [local_addr EXCEPT ![n] = addr]
    /\ table' = [table EXCEPT ![s] = addr]


SetItemUnlock(n) ==
    LET
        addr == local_addr[n]
        obj == global_mem[addr]
        s == obj.slot
    IN
    /\ pc[n] = "SetItemUnlock"
    /\ goto(n, "Terminated")

    /\ local_addr' = [local_addr EXCEPT ![n] = nil]
    /\ unlock_slot(s)

    /\ UNCHANGED next_val
    /\ UNCHANGED global_mem
    /\ UNCHANGED table

---------------------------------------------------------------------

TerminateCond ==
    /\ \A n \in Node: pc[n] = "Terminated"

Terminated ==
    /\ TerminateCond
    /\ UNCHANGED vars


Next ==
    \/ \E n \in Node, s \in Slot:
        \/ SetNewItem(n, s)
    \/ \E n \in Node:
        \/ SetItemUnlock(n)
    \/ Terminated

Spec == Init /\ [][Next]_vars

---------------------------------------------------------------------

ItemActiveOrFreeInv ==
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

====

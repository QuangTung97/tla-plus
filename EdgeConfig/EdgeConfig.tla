------ MODULE EdgeConfig ----
EXTENDS TLC, Naturals, Sequences

CONSTANTS Key, SyncSlave, nil, max_val

VARIABLES
    db, mem, key_slave, next_val,
    global_chan, wait_chan,
    slave_db, pc, local_chan

core_vars == <<db, mem, next_val, wait_chan>>

aux_vars == <<key_slave>>

slave_vars == <<
    slave_db, pc, local_chan
>>

vars == <<
    core_vars, global_chan, slave_vars, aux_vars
>>
----------------------------------------------------------------------------

Value == 21..max_val

NullValue == Value \union {nil}

Channel == DOMAIN global_chan

NullChan == Channel \union {nil}

Config == [
    updated: SUBSET (Key \X Value)
]

ChannelData == [
    data: Seq(Config)
]

----------------------------------------------------------------------------

TypeOK ==
    /\ db \in [Key -> NullValue]
    /\ mem \in [Key -> NullValue]
    /\ key_slave \in [Key -> SyncSlave]
    /\ global_chan \in Seq(ChannelData)
    /\ wait_chan \in [SyncSlave -> NullChan]

    /\ slave_db \in [SyncSlave -> [Key -> NullValue]]
    /\ pc \in [SyncSlave -> {"Init"}]
    /\ local_chan \in [SyncSlave -> NullChan]

    /\ next_val \in 20..max_val

Init ==
    /\ db = [k \in Key |-> nil]
    /\ mem = [k \in Key |-> nil]
    /\ key_slave \in [Key -> SyncSlave]
    /\ global_chan = <<>>
    /\ wait_chan = [s \in SyncSlave |-> nil]

    /\ slave_db = [s \in SyncSlave |-> [k \in Key |-> nil]]
    /\ pc = [s \in SyncSlave |-> "Init"]
    /\ local_chan = [s \in SyncSlave |-> nil]

    /\ next_val = 20

----------------------------------------------------------------------------

keys_of_slave(s) ==
    {k \in Key: key_slave[k] = s}


UpdateDB(k) ==
    /\ next_val < max_val
    /\ next_val' = next_val + 1
    /\ db' = [db EXCEPT ![k] = next_val']
    /\ UNCHANGED mem
    /\ UNCHANGED global_chan
    /\ UNCHANGED wait_chan
    /\ UNCHANGED slave_vars
    /\ UNCHANGED aux_vars


UpdateMem ==
    LET
        changed_keys(s) == {k \in Key: key_slave[k] = s /\ mem[k] # db[k]}
    IN
    /\ mem # db
    /\ mem' = db
    /\ UNCHANGED global_chan
    /\ UNCHANGED wait_chan
    /\ UNCHANGED db
    /\ UNCHANGED next_val
    /\ UNCHANGED slave_vars
    /\ UNCHANGED aux_vars

----------------------------------------------------------------------------

SetupChan(s) ==
    /\ pc[s] = "Init"
    /\ UNCHANGED core_vars

----------------------------------------------------------------------------

TerminateCond ==
    /\ mem = db
    /\ \A s \in SyncSlave: pc[s] = "WaitOnChan"

Terminated ==
    /\ TerminateCond
    /\ UNCHANGED vars


Next ==
    \/ \E k \in Key:
        \/ UpdateDB(k)
    \/ \E s \in SyncSlave:
        \/ SetupChan(s)
    \/ UpdateMem
    \/ Terminated

Spec == Init /\ [][Next]_vars

----------------------------------------------------------------------------

SlaveDBMatchDB ==
    LET
        cond ==
            \A s \in SyncSlave: \A k \in keys_of_slave(s):
                db[k] = slave_db[s][k]

    IN
        TerminateCond => cond

====

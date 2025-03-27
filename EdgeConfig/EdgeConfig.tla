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
    updated_keys: SUBSET Key, \* TODO not allow empty
    updated_vals: [Key -> NullValue]
]

ChannelData == Seq(Config)

PC == {"Init", "WaitOnChan"}

----------------------------------------------------------------------------

TypeOK ==
    /\ db \in [Key -> NullValue]
    /\ mem \in [Key -> NullValue]
    /\ key_slave \in [Key -> SyncSlave]
    /\ global_chan \in Seq(ChannelData)
    /\ wait_chan \in [SyncSlave -> NullChan]

    /\ slave_db \in [SyncSlave -> [Key -> NullValue]]
    /\ pc \in [SyncSlave -> PC]
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


slave_of_chan(ch) ==
    CHOOSE s \in SyncSlave: wait_chan[s] = ch


UpdateMem ==
    LET
        changed_keys(s) == {k \in Key: key_slave[k] = s /\ mem[k] # db[k]}

        pushed_slaves == {
            s \in SyncSlave:
                /\ wait_chan[s] # nil
                /\ changed_keys(s) # {}
        }

        pushed_chans == {wait_chan[s]: s \in pushed_slaves}

        push_to(old, ch) ==
            LET
                s == slave_of_chan(ch)

                conf == [
                    updated_keys |-> changed_keys(s),
                    updated_vals |-> mem'
                ]
            IN
                IF ch \in pushed_chans
                    THEN Append(old, conf)
                    ELSE old

        push ==
            global_chan' = [
                idx \in DOMAIN global_chan |->
                    push_to(global_chan[idx], idx)]
    IN
    /\ mem # db
    /\ mem' = db
    /\ push
    /\ UNCHANGED wait_chan
    /\ UNCHANGED db
    /\ UNCHANGED next_val
    /\ UNCHANGED slave_vars
    /\ UNCHANGED aux_vars

----------------------------------------------------------------------------

goto(s, l) ==
    pc' = [pc EXCEPT ![s] = l]


SetupChan(s) ==
    LET
        non_nil_keys == {k \in Key: key_slave[k] = s /\ mem[k] # nil}

        conf == [
            updated_keys |-> non_nil_keys,
            updated_vals |-> mem
        ]

        new_ch == <<conf>>

        ch == Len(global_chan')
    IN
    /\ pc[s] = "Init"
    /\ goto(s, "WaitOnChan")
    /\ global_chan' = Append(global_chan, new_ch)
    /\ local_chan' = [local_chan EXCEPT ![s] = ch]
    /\ wait_chan' = [wait_chan EXCEPT ![s] = ch]
    /\ UNCHANGED <<db, mem, next_val>>
    /\ UNCHANGED slave_db
    /\ UNCHANGED aux_vars

----------------------------------------------------------------------------

TerminateCond ==
    /\ mem = db
    /\ \A s \in SyncSlave:
        /\ pc[s] = "WaitOnChan"
        /\ global_chan[local_chan[s]] = <<>>

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

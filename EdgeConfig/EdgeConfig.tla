------ MODULE EdgeConfig ----
EXTENDS TLC, Naturals, Sequences

CONSTANTS Key, SyncSlave, nil, max_val

VARIABLES
    db, mem, key_slave, next_val,
    global_chan, wait_chan, wait_status, slave_changes,
    slave_db, pc, local_chan

core_vars == <<
    db, mem, next_val, wait_chan, wait_status, slave_changes
>>

aux_vars == <<key_slave>>

slave_vars == <<
    slave_db, pc, local_chan
>>

vars == <<
    core_vars, global_chan, slave_vars, aux_vars
>>

----------------------------------------------------------------------------

update_fn_multi(fn, update_fn(_, _)) ==
    fn' = [x \in DOMAIN fn |-> update_fn(x, fn[x])]

----------------------------------------------------------------------------

Value == 21..max_val

NullValue == Value \union {nil}

Channel == DOMAIN global_chan

NullChan == Channel \union {nil}

Config == [
    updated_keys: SUBSET Key,
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
    /\ wait_status \in [SyncSlave -> {"Nil", "Connected"}]
    /\ slave_changes \in [SyncSlave -> SUBSET Key]

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
    /\ wait_status = [s \in SyncSlave |-> "Nil"]
    /\ slave_changes = [s \in SyncSlave |-> {}]

    /\ slave_db = [s \in SyncSlave |-> [k \in Key |-> nil]]
    /\ pc = [s \in SyncSlave |-> "Init"]
    /\ local_chan = [s \in SyncSlave |-> nil]

    /\ next_val = 20

----------------------------------------------------------------------------

keys_of_slave(s) ==
    {k \in Key: key_slave[k] = s}

mem_with_keys(keys) ==
    [k \in DOMAIN mem' |-> IF k \in keys THEN mem'[k] ELSE nil]


UpdateDB(k) ==
    /\ next_val < max_val
    /\ next_val' = next_val + 1
    /\ db' = [db EXCEPT ![k] = next_val']
    /\ UNCHANGED mem
    /\ UNCHANGED global_chan
    /\ UNCHANGED <<wait_chan, wait_status, slave_changes>>
    /\ UNCHANGED slave_vars
    /\ UNCHANGED aux_vars


slave_of_chan(ch) ==
    CHOOSE s \in SyncSlave: wait_chan[s] = ch


UpdateMem ==
    LET
        changed_keys(s) == {k \in Key: key_slave[k] = s /\ mem[k] # db[k]}

        changed_slaves == {s \in SyncSlave: changed_keys(s) # {}}

        pushed_slaves == {s \in changed_slaves: /\ wait_chan[s] # nil}

        pushed_chans == {wait_chan[s]: s \in pushed_slaves}

        push_to(old, ch) ==
            LET
                s == slave_of_chan(ch)

                conf == [
                    updated_keys |-> changed_keys(s),
                    updated_vals |-> mem_with_keys(changed_keys(s))
                ]
            IN
                IF ch \in pushed_chans
                    THEN Append(old, conf)
                    ELSE old

        push_to_clients ==
            global_chan' = [
                idx \in DOMAIN global_chan |->
                    push_to(global_chan[idx], idx)]

        update_wait_ch(s, old) ==
            IF s \in pushed_slaves
                THEN nil
                ELSE old

        update_slave_changes(s, old) ==
            IF s \in (changed_slaves \ pushed_slaves)
                THEN changed_keys(s) \* TODO
                ELSE old
    IN
    /\ mem # db
    /\ mem' = db
    /\ push_to_clients
    /\ update_fn_multi(wait_chan, update_wait_ch)
    /\ update_fn_multi(slave_changes, update_slave_changes)
    /\ UNCHANGED wait_status
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
            updated_vals |-> mem_with_keys(non_nil_keys)
        ]

        ch == Len(global_chan')

        when_first_connect ==
            /\ global_chan' = Append(global_chan, <<conf>>)
            /\ local_chan' = [local_chan EXCEPT ![s] = ch]
            /\ wait_status' = [wait_status EXCEPT ![s] = "Connected"]
            /\ slave_changes' = [slave_changes EXCEPT ![s] = {}] \* TODO Inv
            /\ UNCHANGED wait_chan

        when_connected_change_empty ==
            /\ global_chan' = Append(global_chan, <<>>)
            /\ wait_chan' = [wait_chan EXCEPT ![s] = ch]

        changed_conf == [
            updated_keys |-> slave_changes[s],
            updated_vals |-> mem_with_keys(slave_changes[s])
        ]

        when_connected_change_non_empty ==
            /\ global_chan' = Append(global_chan, <<changed_conf>>)
            /\ wait_chan' = [wait_chan EXCEPT ![s] = nil]

        when_connected ==
            /\ IF slave_changes[s] = {}
                THEN when_connected_change_empty
                ELSE when_connected_change_non_empty
            /\ local_chan' = [local_chan EXCEPT ![s] = ch]
            /\ slave_changes' = [slave_changes EXCEPT ![s] = {}]
            /\ UNCHANGED wait_status
    IN
    /\ pc[s] = "Init"
    /\ goto(s, "WaitOnChan")
    /\ UNCHANGED mem

    /\ IF wait_status[s] = "Nil"
        THEN when_first_connect
        ELSE when_connected

    /\ UNCHANGED <<db, next_val>>
    /\ UNCHANGED slave_db
    /\ UNCHANGED aux_vars


ConsumeChan(s) ==
    LET
        ch == local_chan[s]

        ev == global_chan[ch][1]

        do_update_key(k, old) ==
            IF k \in ev.updated_keys
                THEN ev.updated_vals[k]
                ELSE old

        update_slave_db(old) ==
            [k \in Key |-> do_update_key(k, old[k])]
    IN
    /\ pc[s] = "WaitOnChan"
    /\ global_chan[ch] # <<>>
    /\ goto(s, "Init")
    /\ global_chan' = [global_chan EXCEPT ![ch] = Tail(@)]
    /\ local_chan' = [local_chan EXCEPT ![s] = nil]
    /\ slave_db' = [slave_db EXCEPT ![s] = update_slave_db(@)]
    /\ UNCHANGED core_vars
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
        \/ ConsumeChan(s)
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


GlobalChanInv ==
    \A ch \in Channel:
        LET
            ev == global_chan[ch][1]

            cond ==
                \A k \in Key:
                    k \notin ev.updated_keys => ev.updated_vals[k] = nil
        IN
        /\ Len(global_chan[ch]) <= 1
        /\ global_chan[ch] # <<>> => cond

====

-- ---- MODULE PendingKeys ----
EXTENDS TLC, Naturals

CONSTANTS Key, Slave, Client, nil

VARIABLES info, pending, pc,
    slave_map,
    client_slave, client_state, client_keys,
    num_action

aux_vars == <<client_slave, num_action>>

vars == <<
    info, pending, pc,
    slave_map,
    client_state, client_keys,
    aux_vars
>>


max_action == 7

Seq == 0..30

NullSlave == Slave \union {nil}

SlaveState == [
    running: SUBSET Key,
    latest_seq: Seq,
    wait_list: SUBSET Client
]

Channel == [data: SUBSET Key, status: {"Empty", "Ready", "Consumed"}]

ClientState == [
    chan: Channel,
    consumed_seq: Seq
]


init_slave_state == [
    running |-> {},
    latest_seq |-> 0,
    wait_list |-> {}
]

init_client_state == [
    chan |-> [data |-> {}, status |-> "Consumed"],
    consumed_seq |-> 0
]

TypeOK ==
    /\ info \in [Key -> NullSlave]
    /\ pending \subseteq Key
    /\ pc \in [Client -> {"Init", "GetRunningKeys", "WaitOnChan"}]
    /\ client_slave \in [Client -> Slave]

    /\ slave_map \in [Slave -> SlaveState]
    /\ client_state \in [Client -> ClientState]
    /\ client_keys \in [Client -> SUBSET Key]
    /\ num_action \in 0..max_action


Init ==
    /\ info = [k \in Key |-> nil]
    /\ pending = {}
    /\ pc = [s \in Client |-> "Init"]
    /\ client_slave \in [Client -> Slave]

    /\ slave_map = [s \in Slave |-> init_slave_state]
    /\ client_state = [c \in Client |-> init_client_state]
    /\ client_keys = [c \in Client |-> {}]
    /\ num_action = 0


allowAction ==
    /\ num_action < max_action
    /\ num_action' = num_action + 1


pushToClient(client_set, old_state) ==
    LET
        get_slave(c) == slave_map'[client_slave[c]]

        curr_seq(c) == get_slave(c).latest_seq

        can_push(c) ==
            /\ c \in client_set
            /\ old_state[c].chan.status = "Empty"
            /\ old_state[c].consumed_seq < curr_seq(c)
        
        new_chan(c) ==
            [data |-> get_slave(c).running, status |-> "Ready"]
        
        new_state(c) ==
            [chan |-> new_chan(c), consumed_seq |-> curr_seq(c)]
        
        new_state_or_unchanged(c) ==
            IF can_push(c)
                THEN new_state(c)
                ELSE old_state[c] \* UNCHANGED
    IN
        [c \in Client |-> new_state_or_unchanged(c)]


AddKey(k) ==
    LET
        added ==
            IF k \in pending
                THEN {}
                ELSE {k}

        add_one(old) ==
            IF k \in pending
                THEN old
                ELSE old + 1
                
        do_add_key(s) ==
            /\ info[k] = nil
            /\ allowAction
            /\ info' = [info EXCEPT ![k] = s]
            /\ slave_map' = [slave_map EXCEPT
                    ![s].latest_seq = add_one(@),
                    ![s].running = @ \union added]
            /\ client_state' = pushToClient(slave_map[s].wait_list, client_state)
            /\ UNCHANGED pending
            /\ UNCHANGED pc
            /\ UNCHANGED client_slave
            /\ UNCHANGED client_keys
    IN
        \E s \in Slave: do_add_key(s)


RemoveKey(k) ==
    LET
        do_remove_key(s) ==
            /\ info[k] # nil
            /\ info[k] = s
            /\ allowAction
            /\ info' = [info EXCEPT ![k] = nil]

            /\ slave_map' = [slave_map EXCEPT
                    ![s].running = @ \ {k},
                    ![s].latest_seq = @ + 1]
            /\ client_state' = pushToClient(slave_map[s].wait_list, client_state)

            /\ UNCHANGED pending
            /\ UNCHANGED pc
            /\ UNCHANGED client_slave
            /\ UNCHANGED client_keys
    IN
        \E s \in Slave: do_remove_key(s)


addPendingKeyUpdateSlaveMap(k) ==
    LET
        s == info[k]
    IN
        /\ slave_map' = [slave_map EXCEPT
                ![s].running = @ \ {k},
                ![s].latest_seq = @ + 1
            ]
        /\ client_state' = pushToClient(slave_map[s].wait_list, client_state)

AddPendingKey(k) ==
    /\ k \notin pending
    /\ allowAction
    /\ pending' = pending \union {k}
    /\ IF info[k] # nil
        THEN addPendingKeyUpdateSlaveMap(k)
        ELSE
            /\ UNCHANGED slave_map
            /\ UNCHANGED client_state
    /\ UNCHANGED info
    /\ UNCHANGED pc
    /\ UNCHANGED client_slave
    /\ UNCHANGED client_keys


removePendingKeyUpdateSlaveMap(k) ==
    LET
        s == info[k]
    IN
        /\ slave_map' = [slave_map EXCEPT
                ![s].running = @ \union {k},
                ![s].latest_seq = @ + 1
            ]
        /\ client_state' = pushToClient(slave_map[s].wait_list, client_state)


RemovePendingKey(k) ==
    /\ k \in pending
    /\ allowAction
    /\ pending' = pending \ {k}

    /\ IF info[k] # nil
        THEN removePendingKeyUpdateSlaveMap(k)
        ELSE
            /\ UNCHANGED slave_map
            /\ UNCHANGED client_state

    /\ UNCHANGED info
    /\ UNCHANGED pc
    /\ UNCHANGED client_slave
    /\ UNCHANGED client_keys


InitClient(c) ==
    LET
        s == client_slave[c]
    IN
        /\ pc[c] = "Init"
        /\ pc' = [pc EXCEPT ![c] = "GetRunningKeys"]
        /\ slave_map' = [slave_map EXCEPT ![s].wait_list = @ \union {c}]
        /\ UNCHANGED client_state
        /\ UNCHANGED client_keys
        /\ UNCHANGED info
        /\ UNCHANGED pending
        /\ UNCHANGED aux_vars


init_channel == [data |-> {}, status |-> "Empty"]

GetRunningKeys(c) ==
    LET
        \* new channel and assign to client_state
        updated_chan == [client_state EXCEPT ![c].chan = init_channel]
    IN
        /\ pc[c] = "GetRunningKeys"
        /\ pc' = [pc EXCEPT ![c] = "WaitOnChan"]

        /\ UNCHANGED slave_map
        /\ client_state' = pushToClient({c}, updated_chan)

        /\ UNCHANGED client_keys
        /\ UNCHANGED info
        /\ UNCHANGED pending
        /\ UNCHANGED aux_vars


ConsumeChan(c) ==
    /\ pc[c] = "WaitOnChan"
    /\ client_state[c].chan.status = "Ready"
    /\ pc' = [pc EXCEPT ![c] = "GetRunningKeys"]
    /\ client_state' = [client_state EXCEPT ![c].chan.status = "Consumed"]
    /\ client_keys' = [client_keys EXCEPT ![c] = client_state[c].chan.data]
    /\ UNCHANGED slave_map
    /\ UNCHANGED info
    /\ UNCHANGED pending
    /\ UNCHANGED aux_vars


clientWaitOnChan(c) ==
    /\ pc[c] = "WaitOnChan"
    /\ client_state[c].chan.status = "Empty"

TerminateCond ==
    /\ \A c \in Client: clientWaitOnChan(c)
    /\ num_action = max_action

Terminated ==
    /\ TerminateCond
    /\ UNCHANGED vars

Next ==
    \/ \E k \in Key:
        \/ AddKey(k)
        \/ RemoveKey(k)
        \/ AddPendingKey(k)
        \/ RemovePendingKey(k)
    \/ \E c \in Client:
        \/ InitClient(c)
        \/ GetRunningKeys(c)
        \/ ConsumeChan(c)
    \/ Terminated


Spec == Init /\ [][Next]_vars

FairSpec == Spec /\ WF_vars(Next)


AlwaysTerminate == <> TerminateCond


running_keys(s) == {k \in Key: info[k] = s} \ pending

ClientKeysMatchSharedState ==
    \A c \in Client:
        clientWaitOnChan(c) =>
            /\ client_keys[c] = running_keys(client_slave[c])


SlaveMapRunningMatchSharedState ==
    \A s \in Slave:
        slave_map[s].running = running_keys(s)


channelAction(c) ==
    \/ /\ client_state[c].chan.status = "Consumed"
       /\ client_state'[c].chan.status = "Empty"
    \/ /\ client_state[c].chan.status = "Consumed"
       /\ client_state'[c].chan.status = "Ready"
    \/ /\ client_state[c].chan.status = "Empty"
       /\ client_state'[c].chan.status = "Ready"
    \/ /\ client_state[c].chan.status = "Ready"
       /\ client_state'[c].chan.status = "Consumed"
    \/ client_state'[c].chan = client_state[c].chan

allChannelAction ==
    \A c \in Client: channelAction(c)

ChannelSpec ==
    [][allChannelAction]_client_state


ReadyAlwaysConsumed ==
    \A c \in Client:
        client_state[c].chan.status = "Ready"
            ~> client_state[c].chan.status = "Consumed"


====

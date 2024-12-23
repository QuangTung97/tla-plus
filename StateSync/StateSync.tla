------ MODULE StateSync ----
EXTENDS TLC, Integers, Sequences

CONSTANTS Key, Client, nil

VARIABLES server_state, wait_list, push_back_list,
    client_keys, client_states,
    next_val, server_pc, client_pc, locked,
    channels, client_channel, client_queue,
    consume_channel, outer_states

vars == <<server_state, wait_list, push_back_list,
    client_keys, client_states,
    next_val, server_pc, client_pc, locked,
    channels, client_channel, client_queue,
    consume_channel, outer_states>>

client_vars == <<
    client_keys, client_states, client_pc,
    consume_channel, outer_states>>

min_val == 21
max_val == 23

Value == min_val..max_val

NullValue == Value \union {nil}

KevVal == [Key -> NullValue]

emptyKV == [k \in Key |-> nil]

Pair == Key \X Value

NullPair == Pair \union {nil}

Channel == [data: NullPair, status: {"Empty", "Ready", "Consumed"}]

ClientState == {"Init", "ClientCheckQueue", "GetFromQueue", "WaitOnChan"}

TypeOK ==
    /\ server_state \in KevVal
    /\ wait_list \in [Key -> SUBSET Client]
    /\ push_back_list \in [Key -> SUBSET Client]
    /\ next_val \in (min_val-1)..max_val
    /\ client_keys \in [Client -> SUBSET Key]
    /\ client_states \in [Client -> KevVal]
    /\ server_pc \in {"Init", "CheckWaitList", "SetBackWaitList"}
    /\ client_pc \in [Client -> ClientState]
    /\ locked \in BOOLEAN
    /\ channels \in Seq(Channel)
    /\ client_channel \in [Client -> 1..Len(channels) \union {nil}]
    /\ client_queue \in [Client -> SUBSET Key]
    /\ consume_channel \in [Client -> 1..Len(channels) \union {nil}]
    /\ outer_states \in [Client -> KevVal]


Init ==
    /\ server_state = emptyKV
    /\ wait_list = [k \in Key |-> {}]
    /\ push_back_list = [k \in Key |-> {}]
    /\ client_keys \in [Client -> SUBSET Key]
    /\ \A c \in Client: client_keys[c] # {} \* client keys should not be empty
    /\ client_states = [c \in Client |-> emptyKV]
    /\ next_val = min_val - 1
    /\ server_pc = "Init"
    /\ client_pc = [c \in Client |-> "Init"]
    /\ locked = FALSE
    /\ channels = <<>>
    /\ client_channel = [c \in Client |-> nil]
    /\ client_queue = [c \in Client |-> client_keys[c]]
    /\ consume_channel = [c \in Client |-> nil]
    /\ outer_states = [c \in Client |-> emptyKV]


waitListEmpty ==
    \A k \in Key: wait_list[k] = {}


SetServerState(k) ==
    /\ next_val < max_val
    /\ ~locked

    /\ server_pc = "Init"
    /\ IF waitListEmpty
        THEN
            /\ UNCHANGED locked
            /\ UNCHANGED server_pc
        ELSE
            /\ locked' = TRUE
            /\ server_pc' = "CheckWaitList"

    /\ next_val' = next_val + 1
    /\ server_state' = [server_state EXCEPT ![k] = next_val']

    /\ UNCHANGED <<wait_list, push_back_list>>
    /\ UNCHANGED channels
    /\ UNCHANGED client_channel
    /\ UNCHANGED client_queue
    /\ UNCHANGED client_vars


setOutputChan(c, k) ==
    LET
        index == client_channel[c]
        oldState == channels[index]
        val == server_state[k]
        newState == [oldState EXCEPT !.data = <<k, val>>, !.status = "Ready"]
    IN
        /\ channels' = [channels EXCEPT ![index] = newState]
        /\ client_channel' = [client_channel EXCEPT ![c] = nil]
        /\ client_states' = [client_states EXCEPT ![c][k] = server_state[k]]


waitListEmptyNew ==
    \A k \in Key: wait_list'[k] = {}


handleWaitEntryNoChange(c, k) ==
    /\ push_back_list' = [push_back_list EXCEPT ![k] = @ \union {c}]
    /\ UNCHANGED channels
    /\ UNCHANGED client_states
    /\ UNCHANGED client_queue
    /\ UNCHANGED client_channel

handleWaitEntryChanged(c, k) ==
    IF client_channel[c] # nil
        THEN
            /\ setOutputChan(c, k)
            /\ client_queue' = [client_queue EXCEPT ![c] = @ \union {k}]
            /\ UNCHANGED push_back_list
        ELSE
            /\ client_queue' = [client_queue EXCEPT ![c] = @ \union {k}]
            /\ UNCHANGED channels
            /\ UNCHANGED client_channel
            /\ UNCHANGED client_states
            /\ UNCHANGED push_back_list

ServerCheckWaitList(k, c) ==
    /\ server_pc = "CheckWaitList"
    /\ c \in wait_list[k]
    /\ wait_list' = [wait_list EXCEPT ![k] = @ \ {c}]

    /\ IF client_states[c][k] = server_state[k]
        THEN handleWaitEntryNoChange(c, k)
        ELSE handleWaitEntryChanged(c, k)

    /\ IF waitListEmptyNew
        THEN
            /\ server_pc' = "SetBackWaitList"
            /\ UNCHANGED locked
        ELSE
            /\ UNCHANGED server_pc
            /\ UNCHANGED locked

    /\ UNCHANGED server_state
    /\ UNCHANGED <<client_keys, client_pc, consume_channel, outer_states>>
    /\ UNCHANGED next_val

ServerSetBackWaitList ==
    /\ server_pc = "SetBackWaitList"
    /\ server_pc' = "Init"
    /\ locked' = FALSE
    /\ wait_list' = push_back_list
    /\ push_back_list' = [k \in Key |-> {}]
    /\ UNCHANGED server_state
    /\ UNCHANGED channels
    /\ UNCHANGED <<client_channel, client_queue>>
    /\ UNCHANGED client_vars
    /\ UNCHANGED next_val


clientGoto(c, state) == client_pc' = [client_pc EXCEPT ![c] = state]

newChannel ==
    /\ channels' = Append(channels, [data |-> nil, status |-> "Empty"])

newChannelIndex == Len(channels')

GetState(c) ==
    /\ client_pc[c] = "Init"
    /\ ~locked
    /\ locked' = TRUE
    /\ newChannel
    /\ client_channel' = [client_channel EXCEPT ![c] = newChannelIndex]
    /\ clientGoto(c, "ClientCheckQueue")
    /\ UNCHANGED <<client_keys, client_states, client_queue>>
    /\ UNCHANGED next_val
    /\ UNCHANGED <<server_pc, server_state>>
    /\ UNCHANGED <<consume_channel, outer_states>>
    /\ UNCHANGED <<wait_list, push_back_list>>


ClientCheckQueue(c) ==
    /\ client_pc[c] = "ClientCheckQueue"
    /\ IF client_queue[c] = {}
        THEN
            /\ clientGoto(c, "WaitOnChan")
            /\ consume_channel' = [consume_channel EXCEPT ![c] = client_channel[c]]
            /\ locked' = FALSE
            /\ UNCHANGED client_channel
        ELSE
            /\ clientGoto(c, "GetFromQueue")
            /\ UNCHANGED locked
            /\ UNCHANGED client_channel
            /\ UNCHANGED consume_channel
    /\ UNCHANGED channels
    /\ UNCHANGED <<client_queue, client_states>>
    /\ UNCHANGED <<client_keys>>
    /\ UNCHANGED <<server_pc, server_state>>
    /\ UNCHANGED next_val
    /\ UNCHANGED <<outer_states>>
    /\ UNCHANGED <<wait_list, push_back_list>>


GetFromQueue(c, k) ==
    /\ client_pc[c] = "GetFromQueue"
    /\ k \in client_queue[c]
    /\ IF client_states[c][k] = server_state[k]
        THEN
            /\ client_queue' = [client_queue EXCEPT ![c] = @ \ {k}]
            /\ clientGoto(c, "ClientCheckQueue")
            /\ wait_list' = [wait_list EXCEPT ![k] = @ \union {c}]
            /\ UNCHANGED channels
            /\ UNCHANGED client_channel
            /\ UNCHANGED client_states
            /\ UNCHANGED locked
            /\ UNCHANGED consume_channel
            /\ UNCHANGED push_back_list
        ELSE
            /\ clientGoto(c, "WaitOnChan")
            /\ locked' = FALSE
            /\ setOutputChan(c, k)
            /\ consume_channel' = [consume_channel EXCEPT ![c] = client_channel[c]]
            /\ UNCHANGED client_queue
            /\ UNCHANGED wait_list
            /\ UNCHANGED push_back_list
    /\ UNCHANGED <<server_pc, server_state>>
    /\ UNCHANGED client_keys
    /\ UNCHANGED next_val
    /\ UNCHANGED outer_states


ConsumeFromChan(c) ==
    LET
        index == consume_channel[c]
        old_state == channels[index]
        k == old_state.data[1]
        val == old_state.data[2]
        new_state == [old_state EXCEPT !.data = nil, !.status = "Consumed"]
    IN
        /\ client_pc[c] = "WaitOnChan"
        /\ channels[index].status = "Ready"
        /\ clientGoto(c, "Init")
        /\ channels' = [channels EXCEPT ![index] = new_state]
        /\ outer_states' = [outer_states EXCEPT ![c][k] = val]
        /\ UNCHANGED <<client_keys, client_states, client_queue, client_channel>>
        /\ UNCHANGED consume_channel
        /\ UNCHANGED locked
        /\ UNCHANGED <<server_pc, server_state, next_val, wait_list>>
        /\ UNCHANGED push_back_list


TerminateCond ==
    /\ server_pc = "Init"
    /\ \A c \in Client:
        /\ client_pc[c] = "WaitOnChan"
        /\ channels[consume_channel[c]].status = "Empty"
    /\ next_val = max_val

Terminated ==
    /\ TerminateCond
    /\ UNCHANGED vars


Next ==
    \/ \E k \in Key:
        \/ SetServerState(k)
    \/ \E c \in Client:
        \/ GetState(c)
        \/ ClientCheckQueue(c)
        \/ \E k \in Key:
            \/ GetFromQueue(c, k)
            \/ ServerCheckWaitList(k, c)
        \/ ConsumeFromChan(c)
    \/ ServerSetBackWaitList
    \/ Terminated


Spec == Init /\ [][Next]_vars

FairSpec == Spec /\ WF_vars(Next)


Inv ==
    TerminateCond =>
        \A c \in Client: \A k \in client_keys[c]:
            /\ client_states[c][k] = server_state[k]
            /\ outer_states[c][k] = server_state[k]


AlwaysTerminate == <> TerminateCond


ChannelInv ==
    \A index \in 1..Len(channels):
        LET
            ch == channels[index]
        IN
            \/ ch.data = nil /\ ch.status = "Empty"
            \/ ch.data = nil /\ ch.status = "Consumed"
            \/ ch.data # nil /\ ch.status = "Ready"

LockedCorrectly ==
    LET
        clientNotLocked(c) ==
            \/ client_pc[c] = "Init"
            \/ client_pc[c] = "WaitOnChan"

        serverAndClientCond ==
            /\ server_pc = "Init"
            /\ \A c \in Client: clientNotLocked(c)
    IN
        serverAndClientCond <=> ~locked


allChannelConsumedExceptWaiting ==
    \A i \in DOMAIN channels:
        (\A c \in Client: consume_channel[c] # i) => channels[i].status = "Consumed"

AllChannelConsumed ==
    TerminateCond => allChannelConsumedExceptWaiting


channelPushOrRecv ==
    \A index \in 1..Len(channels):
        LET
            before == channels[index]
            after == channels'[index]
        IN
            \/ /\ before.status = "Empty"
               /\ after.status = "Ready"
            \/ /\ before.status = "Ready"
               /\ after.status = "Consumed"
            \/ before = after

channelPushRecvOrAppend ==
    \/ channelPushOrRecv
    \/ Len(channels') = Len(channels) + 1

ChannelPushInv ==
    [][channelPushRecvOrAppend]_channels


waitListMustNotDuplicatedCond ==
    LET
        checkCond(c) ==
            /\ client_pc[c] = "GetFromQueue"
            /\ client_pc'[c] = "ClientCheckQueue"
    IN
        \A c \in Client:
            checkCond(c) => wait_list' # wait_list

WaitListNotDuplicated == [][waitListMustNotDuplicatedCond]_client_pc


clientWaitOnChanToInit ==
    LET
        checkCond(c) == client_pc[c] = "WaitOnChan" /\ client_pc'[c] = "Init"
        stateMustChange(c) == outer_states[c] # outer_states'[c]
    IN
        \A c \in Client: checkCond(c) => stateMustChange(c)

ConsumeFromChannelAlwaysCauseChange ==
    [][clientWaitOnChanToInit]_client_pc


Symm == Permutations(Key) \union Permutations(Client)

====
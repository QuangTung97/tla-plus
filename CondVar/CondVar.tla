------ MODULE CondVar ----
EXTENDS TLC, Naturals, Sequences, FiniteSets

CONSTANTS Producer, Consumer, nil, max_num_cmd

-----------------------------------------------------

VARIABLES queue, current_cmd, wait_set, wait_count,
    producer_pc, consumer_pc,
    global_ctx, global_chan, disable_cancel,
    local_ctx, local_chan, handle_cmd

safe_vars == <<queue, current_cmd, wait_set, wait_count>>
producer_vars == <<producer_pc>>
consumer_vars == <<consumer_pc, local_ctx, local_chan, handle_cmd>>
vars == <<
    safe_vars,
    global_ctx, global_chan, disable_cancel,
    producer_vars, consumer_vars
>>

-----------------------------------------------------

max_cmd == 20 + max_num_cmd
Cmd == 20..max_cmd
NullCmd == Cmd \union {nil}

ProducerPC == {"Init", "Terminated"}
ConsumerPC == {"Init", "NewChan", "Wait", "WaitOnChan", "Handle", "Terminated"}

CtxState == {"Active", "Cancelled"}
CtxKey == DOMAIN global_ctx
NullCtx == CtxKey \union {nil}

Channel == {"Active", "Closed"}
ChanAddr == DOMAIN global_chan
NullChan == ChanAddr \union {nil}

-----------------------------------------------------

TypeOK ==
    /\ queue \in Seq(Cmd)
    /\ current_cmd \in Cmd
    /\ wait_set \subseteq ChanAddr
    /\ wait_count \in 0..10

    /\ producer_pc \in [Producer -> ProducerPC]
    /\ consumer_pc \in [Consumer -> ConsumerPC]

    /\ global_ctx \in Seq(CtxState)
    /\ local_ctx \in [Consumer -> NullCtx]

    /\ global_chan \in Seq(Channel)
    /\ local_chan \in [Consumer -> NullChan]

    /\ handle_cmd \in [Consumer -> NullCmd]
    /\ disable_cancel \in BOOLEAN

Init ==
    /\ queue = <<>>
    /\ current_cmd = 20
    /\ wait_set = {}
    /\ wait_count = 0

    /\ producer_pc = [p \in Producer |-> "Init"]
    /\ consumer_pc = [c \in Consumer |-> "Init"]

    /\ global_ctx = <<>>
    /\ local_ctx = [c \in Consumer |-> nil]

    /\ global_chan = <<>>
    /\ local_chan = [c \in Consumer |-> nil]

    /\ handle_cmd = [c \in Consumer |-> nil]
    /\ disable_cancel = FALSE

-----------------------------------------------------

ProducerSend(p) ==
    LET
        notify_wait_set ==
            \E ch \in wait_set:
                /\ wait_set' = wait_set \ {ch}
                /\ wait_count' = wait_count - 1
                /\ global_chan' = [global_chan EXCEPT ![ch] = "Closed"]
    IN
    /\ producer_pc[p] = "Init"
    /\ current_cmd < max_cmd

    /\ current_cmd' = current_cmd + 1
    /\ queue' = Append(queue, current_cmd')
    /\ producer_pc' = [producer_pc EXCEPT ![p] = "Terminated"]

    /\ IF wait_set # {}
        THEN notify_wait_set
        ELSE
            /\ UNCHANGED wait_set
            /\ UNCHANGED wait_count
            /\ UNCHANGED global_chan

    /\ UNCHANGED global_ctx
    /\ UNCHANGED consumer_vars
    /\ UNCHANGED disable_cancel

-----------------------------------------------------

ConsumerNewContext(c) ==
    LET
        ctx == "Active"
    IN
    /\ consumer_pc[c] = "Init"
    /\ consumer_pc' = [consumer_pc EXCEPT ![c] = "NewChan"]

    /\ global_ctx' = Append(global_ctx, ctx)
    /\ local_ctx' = [local_ctx EXCEPT ![c] = Len(global_ctx')]

    /\ UNCHANGED safe_vars
    /\ UNCHANGED <<global_chan, local_chan, handle_cmd>>
    /\ UNCHANGED producer_vars
    /\ UNCHANGED disable_cancel

----------------------------------

ConsumerNewChan(c) ==
    /\ consumer_pc[c] = "NewChan"
    /\ consumer_pc' = [consumer_pc EXCEPT ![c] = "Wait"]

    /\ global_chan' = Append(global_chan, "Active")
    /\ local_chan' = [local_chan EXCEPT ![c] = Len(global_chan')]

    /\ UNCHANGED <<global_ctx, local_ctx, handle_cmd>>
    /\ UNCHANGED safe_vars
    /\ UNCHANGED producer_vars
    /\ UNCHANGED disable_cancel

----------------------------------

ConsumerWait(c) ==
    LET
        ch == local_chan[c]

        when_need_wait ==
            /\ consumer_pc' = [consumer_pc EXCEPT ![c] = "WaitOnChan"]
            /\ wait_set' = wait_set \union {ch}
            /\ wait_count' = wait_count + 1
            /\ UNCHANGED queue
            /\ UNCHANGED handle_cmd

        when_ok ==
            /\ consumer_pc' = [consumer_pc EXCEPT ![c] = "Handle"]
            /\ queue' = Tail(queue)
            /\ handle_cmd' = [handle_cmd EXCEPT ![c] = queue[1]]
            /\ UNCHANGED wait_set
            /\ UNCHANGED wait_count
    IN
    /\ consumer_pc[c] = "Wait"
    /\ IF Len(queue) = 0
        THEN when_need_wait
        ELSE when_ok

    /\ UNCHANGED <<local_ctx, local_chan>>
    /\ UNCHANGED current_cmd
    /\ UNCHANGED global_chan
    /\ UNCHANGED global_ctx
    /\ UNCHANGED producer_vars
    /\ UNCHANGED disable_cancel

----------------------------------

clearLocals(c) ==
    /\ handle_cmd' = [handle_cmd EXCEPT ![c] = nil]
    /\ local_ctx' = [local_ctx EXCEPT ![c] = nil]
    /\ local_chan' = [local_chan EXCEPT ![c] = nil]


notifyOther(ch) ==
    LET
        new_set == wait_set \ {ch}
        new_count ==
            IF ch \in wait_set
                THEN wait_count - 1
                ELSE wait_count

        when_do_nothing ==
            /\ wait_set' = new_set
            /\ wait_count' = new_count
            /\ UNCHANGED global_chan
            /\ UNCHANGED queue
            /\ UNCHANGED current_cmd

        notify_single(input_set) ==
            \E x \in input_set:
                /\ global_chan' = [global_chan EXCEPT ![x] = "Closed"]
                /\ wait_set' = input_set \ {x}
                /\ wait_count' = new_count - 1
                /\ UNCHANGED queue
                /\ UNCHANGED current_cmd
    IN
    IF ch \in wait_set \/ new_set = {} THEN
        when_do_nothing
    ELSE
        notify_single(new_set)

ConsumerWaitOnChan(c) ==
    LET
        ch == local_chan[c]
        ctx == local_ctx[c]

        when_chan_ready ==
            /\ global_chan[ch] = "Closed"
            /\ consumer_pc' = [consumer_pc EXCEPT ![c] = "Init"]
            /\ clearLocals(c)
            /\ UNCHANGED global_chan
            /\ UNCHANGED safe_vars

        when_ctx_cancel ==
            /\ global_ctx[ctx] = "Cancelled"
            /\ consumer_pc' = [consumer_pc EXCEPT ![c] = "Terminated"]
            /\ notifyOther(ch)
            /\ clearLocals(c)
    IN
    /\ consumer_pc[c] = "WaitOnChan"
    /\ \/ when_chan_ready
       \/ when_ctx_cancel

    /\ UNCHANGED <<global_ctx>>
    /\ UNCHANGED producer_vars
    /\ UNCHANGED disable_cancel

----------------------------------

ConsumerHandle(c) ==
    /\ consumer_pc[c] = "Handle"
    /\ consumer_pc' = [consumer_pc EXCEPT ![c] = "Terminated"]

    /\ clearLocals(c)
    /\ UNCHANGED <<global_ctx, global_chan>>
    /\ UNCHANGED safe_vars
    /\ UNCHANGED producer_vars
    /\ UNCHANGED disable_cancel

-----------------------------------------------------

doCancelCtx(ctx) ==
    /\ global_ctx[ctx] = "Active"
    /\ ~disable_cancel
    /\ global_ctx' = [global_ctx EXCEPT ![ctx] = "Cancelled"]

    /\ UNCHANGED global_chan
    /\ UNCHANGED safe_vars
    /\ UNCHANGED producer_vars
    /\ UNCHANGED consumer_vars
    /\ UNCHANGED disable_cancel

CancelCtx ==
    \E ctx \in CtxKey: doCancelCtx(ctx)


DoDisableCancel ==
    /\ ~disable_cancel
    /\ disable_cancel' = TRUE

    /\ UNCHANGED <<global_ctx, global_chan>>
    /\ UNCHANGED safe_vars
    /\ UNCHANGED producer_vars
    /\ UNCHANGED consumer_vars

-----------------------------------------------------

TerminateCond ==
    /\ disable_cancel
    /\ \A p \in Producer: producer_pc[p] = "Terminated"
    /\ \A c \in Consumer:
        \/ consumer_pc[c] = "Terminated"
        \/ consumer_pc[c] = "WaitOnChan" /\ queue = <<>>

Terminated ==
    /\ TerminateCond
    /\ UNCHANGED vars


Next ==
    \/ \E p \in Producer:
        \/ ProducerSend(p)
    \/ \E c \in Consumer:
        \/ ConsumerNewContext(c)
        \/ ConsumerNewChan(c)
        \/ ConsumerWait(c)
        \/ ConsumerWaitOnChan(c)
        \/ ConsumerHandle(c)
    \/ CancelCtx
    \/ DoDisableCancel
    \/ Terminated

Spec == Init /\ [][Next]_vars

FairSpec == Spec /\ WF_vars(Next)

-----------------------------------------------------

AlwaysTerminate == []<>TerminateCond

WaitCountMatchWaitSet ==
    wait_count = Cardinality(wait_set)


LocalVarsInv ==
    LET
        is_empty(c) ==
            /\ local_ctx[c] = nil
            /\ local_chan[c] = nil
            /\ handle_cmd[c] = nil

        cond(c) ==
            is_empty(c) <=> consumer_pc[c] \in {"Init", "Terminated"}
    IN
        \A c \in Consumer: cond(c)

====

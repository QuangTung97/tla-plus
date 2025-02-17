------ MODULE MSI ----
EXTENDS TLC, Integers, Sequences, FiniteSets

CONSTANTS Line, CPU, max_value, nil

VARIABLES cache, llc, mem, cache_to_llc, llc_to_cache, cpu_network,
    global_data, stopped

vars == <<cache, llc, mem, cache_to_llc, llc_to_cache, cpu_network,
    global_data, stopped>>

----------------------------------------------------------

NullCPU == CPU \union {nil}

Value == 20..29

NullValue == Value \union {nil}

CacheStatus == {"I", "S", "M"} \* Stable States

CacheTransientStatus == {
    "IS_D", "IM_AD", "IM_A", "SM_AD", "SM_A",
    "SI_A", "MI_A", "II" \* TODO do we need II?
}

ReadableStatus == {"S", "M", "SM_AD", "SM_A"}

WritableStatus == {"M"}

CacheInfo == [
    status: CacheStatus \union CacheTransientStatus,
    data: NullValue,
    need_ack: -10..10
]

LLCActiveStatus == {"None"}

LLCInfo == [
    status: CacheStatus \union {"S_D"},
    active_status: LLCActiveStatus,
    owner: NullCPU,
    sharer: SUBSET CPU,
    data: NullValue
]


GetReq == [
    type: {"GetS", "GetM", "PutS"},
    line: Line
]

DataMResp == [
    type: {"DataM"},
    line: Line,
    data: Value
]

PutMReq == [
    type: {"PutM"},
    line: Line,
    data: Value
]

CacheToLLC == Seq(GetReq \union DataMResp \union PutMReq)


FwdGetType == [
    type: {"Fwd-GetS", "Fwd-GetM"},
    req_cpu: CPU,
    line: Line
]

PutAckType == [
    type: {"Put-Ack"},
    line: Line
]

InvType == [
    type: {"Inv"},
    req_cpu: CPU,
    line: Line
]

DataRespType == [
    type: {"DataResp"},
    line: Line,
    data: Value,
    ack: 0..10
]

LLCToCache == Seq(DataRespType \union FwdGetType \union InvType \union PutAckType)


CpuNetwork ==
    LET
        InvAckMsg == [
            type: {"Inv-Ack"},
            from_cpu: CPU,
            to_cpu: CPU,
            line: Line
        ]

        DataToReqMsg == [
            type: {"DataToReq"},
            from_cpu: CPU,
            to_cpu: CPU,
            line: Line,
            data: Value
        ]
    IN
        InvAckMsg \union DataToReqMsg

----------------------------------------------------------

TypeOK ==
    /\ cache \in [CPU -> [Line -> CacheInfo]]
    /\ llc \in [Line -> LLCInfo]
    /\ mem \in [Line -> Value]
    /\ cache_to_llc \in [CPU -> CacheToLLC]
    /\ llc_to_cache \in [CPU -> LLCToCache]
    /\ cpu_network \subseteq CpuNetwork
    /\ global_data \in [Line -> Value]
    /\ stopped \in BOOLEAN


init_cache == [
    status |-> "I",
    data |-> nil,
    need_ack |-> 0
]

init_llc == [
    status |-> "I",
    active_status |-> "None",
    owner |-> nil,
    sharer |-> {},
    data |-> nil
]

Init ==
    /\ cache = [c \in CPU |-> [l \in Line |-> init_cache]]
    /\ llc = [l \in Line |-> init_llc]
    /\ mem = [l \in Line |-> 20]
    /\ cache_to_llc = [c \in CPU |-> <<>>]
    /\ llc_to_cache = [c \in CPU |-> <<>>]
    /\ cpu_network = {}
    /\ global_data = [l \in Line |-> 20]
    /\ stopped = FALSE

----------------------------------------------------------

cpu_unchanged ==
    /\ UNCHANGED <<llc, mem>>
    /\ UNCHANGED global_data
    /\ UNCHANGED stopped

CpuLoad(c, l) ==
    LET
        new_req == [
            type |-> "GetS",
            line |-> l
        ]
    IN
    /\ cache[c][l].status = "I"
    /\ ~stopped
    /\ cache' = [cache EXCEPT ![c][l].status = "IS_D"]
    /\ cache_to_llc' = [cache_to_llc EXCEPT
            ![c] = Append(@, new_req)
        ]

    /\ cpu_unchanged
    /\ UNCHANGED llc_to_cache
    /\ UNCHANGED cpu_network


CpuDataDir(c, l) ==
    LET
        resp == llc_to_cache[c][1]

        when_is_d ==
            /\ cache[c][l].status = "IS_D"
            /\ cache' = [cache EXCEPT
                    ![c][l].status = "S",
                    ![c][l].data = resp.data
                ]
            /\ UNCHANGED cpu_network

        ack_is_zero ==
            \/ resp.ack = 0
            \/ cache[c][l].need_ack + resp.ack = 0

        when_im_ad_ack_zero ==
            /\ cache[c][l].status = "IM_AD"
            /\ ack_is_zero
            /\ cache' = [cache EXCEPT
                    ![c][l].status = "M",
                    ![c][l].data = resp.data,
                    ![c][l].need_ack = 0
                ]
            /\ UNCHANGED cpu_network

        when_im_ad_ack_non_zero ==
            /\ cache[c][l].status = "IM_AD"
            /\ ~ack_is_zero
            /\ cache' = [cache EXCEPT
                    ![c][l].status = "IM_A",
                    ![c][l].data = resp.data,
                    ![c][l].need_ack = @ + resp.ack
                ]
            /\ UNCHANGED cpu_network

        when_sm_ad_ack_zero ==
            /\ cache[c][l].status = "SM_AD"
            /\ ack_is_zero
            /\ cache' = [cache EXCEPT
                    ![c][l].status = "M",
                    ![c][l].need_ack = 0
                ]
            /\ UNCHANGED cpu_network

        when_sm_ad_ack_non_zero ==
            /\ cache[c][l].status = "SM_AD"
            /\ ~ack_is_zero
            /\ cache' = [cache EXCEPT
                    ![c][l].status = "SM_A",
                    ![c][l].need_ack = @ + resp.ack
                ]
            /\ UNCHANGED cpu_network
    IN
    /\ llc_to_cache[c] # <<>>
    /\ resp.line = l
    /\ resp.type = "DataResp"

    /\ llc_to_cache' = [llc_to_cache EXCEPT ![c] = Tail(@)]
    /\ \/ when_is_d
       \/ when_im_ad_ack_zero
       \/ when_im_ad_ack_non_zero
       \/ when_sm_ad_ack_zero
       \/ when_sm_ad_ack_non_zero

    /\ UNCHANGED cache_to_llc
    /\ cpu_unchanged


CpuRequestStore(c, l) ==
    LET
        new_req == [
            type |-> "GetM",
            line |-> l
        ]

        when_i ==
            /\ cache[c][l].status = "I"
            /\ cache' = [cache EXCEPT ![c][l].status = "IM_AD"]
            /\ cache_to_llc' = [cache_to_llc EXCEPT
                    ![c] = Append(@, new_req)
                ]

        when_s ==
            /\ cache[c][l].status = "S"
            /\ cache' = [cache EXCEPT ![c][l].status = "SM_AD"]
            /\ cache_to_llc' = [cache_to_llc EXCEPT
                    ![c] = Append(@, new_req)
                ]
    IN
    /\ ~stopped
    /\ \/ when_i
       \/ when_s

    /\ UNCHANGED llc_to_cache
    /\ UNCHANGED cpu_network
    /\ cpu_unchanged


CpuUpdate(c, l) ==
    /\ cache[c][l].status \in WritableStatus
    /\ cache[c][l].data <= max_value
    /\ cache' = [cache EXCEPT
            ![c][l].data = @ + 1
        ]
    /\ global_data' = [global_data EXCEPT ![l] = cache'[c][l].data]

    /\ UNCHANGED llc_to_cache
    /\ UNCHANGED cpu_network
    /\ UNCHANGED cache_to_llc
    /\ UNCHANGED <<llc, mem>>
    /\ UNCHANGED stopped

CpuFwdGetS(c, l) ==
    LET
        resp == llc_to_cache[c][1]

        dir_data == [
            type |-> "DataM",
            line |-> l,
            data |-> cache[c][l].data
        ]

        push_to_llc ==
            cache_to_llc' = [cache_to_llc EXCEPT ![c] = Append(@, dir_data)]

        data_to_req_msg == [
            type |-> "DataToReq",
            from_cpu |-> c,
            to_cpu |-> resp.req_cpu,
            line |-> l,
            data |-> cache[c][l].data
        ]

        when_mutable ==
            /\ cache[c][l].status = "M"
            /\ cache' = [cache EXCEPT
                    ![c][l].status = "S"
                ]
            /\ push_to_llc
            /\ cpu_network' = cpu_network \union {data_to_req_msg}

        when_mi_a ==
            /\ cache[c][l].status = "MI_A"
            /\ cache' = [cache EXCEPT
                    ![c][l].status = "SI_A"
                ]
            /\ push_to_llc
            /\ cpu_network' = cpu_network \union {data_to_req_msg}
    IN
    /\ llc_to_cache[c] # <<>>
    /\ resp.line = l
    /\ resp.type = "Fwd-GetS"

    /\ llc_to_cache' = [llc_to_cache EXCEPT ![c] = Tail(@)]
    /\ \/ when_mutable
       \/ when_mi_a

    /\ cpu_unchanged


CpuFwdGetM(c, l) ==
    LET
        resp == llc_to_cache[c][1]

        data_to_req_msg == [
            type |-> "DataToReq",
            from_cpu |-> c,
            to_cpu |-> resp.req_cpu,
            line |-> l,
            data |-> cache[c][l].data
        ]

        when_mutable ==
            /\ cache[c][l].status = "M"
            /\ cache' = [cache EXCEPT
                    ![c][l].status = "I",
                    ![c][l].data = nil
                ]
            /\ cpu_network' = cpu_network \union {data_to_req_msg}

        when_mi_a ==
            /\ cache[c][l].status = "MI_A"
            /\ cache' = [cache EXCEPT
                    ![c][l].status = "II"
                ]
            /\ cpu_network' = cpu_network \union {data_to_req_msg}
    IN
    /\ llc_to_cache[c] # <<>>
    /\ resp.line = l
    /\ resp.type = "Fwd-GetM"

    /\ llc_to_cache' = [llc_to_cache EXCEPT ![c] = Tail(@)]
    /\ \/ when_mutable
       \/ when_mi_a

    /\ UNCHANGED cache_to_llc
    /\ cpu_unchanged


CpuInv(c, l) ==
    LET
        resp == llc_to_cache[c][1]

        inv_ack_msg == [
            type |-> "Inv-Ack",
            from_cpu |-> c,
            to_cpu |-> resp.req_cpu,
            line |-> l
        ]

        when_shared ==
            /\ cache[c][l].status = "S"
            /\ cache' = [cache EXCEPT
                    ![c][l].status = "I",
                    ![c][l].data = nil
                ]
            /\ cpu_network' = cpu_network \union {inv_ack_msg}

        when_sm_ad ==
            /\ cache[c][l].status = "SM_AD"
            /\ cache' = [cache EXCEPT
                    ![c][l].status = "IM_AD"
                ]
            /\ cpu_network' = cpu_network \union {inv_ack_msg}

        when_si_a ==
            /\ cache[c][l].status = "SI_A"
            /\ cache' = [cache EXCEPT
                    ![c][l].status = "II"
                ]
            /\ cpu_network' = cpu_network \union {inv_ack_msg}
    IN
    /\ llc_to_cache[c] # <<>>
    /\ resp.line = l
    /\ resp.type = "Inv"

    /\ llc_to_cache' = [llc_to_cache EXCEPT ![c] = Tail(@)]
    /\ \/ when_shared
       \/ when_sm_ad
       \/ when_si_a

    /\ UNCHANGED cache_to_llc
    /\ cpu_unchanged


CpuInvAck(c, l) ==
    \E msg \in cpu_network:
        LET
            when_im_ad ==
                /\ cache[c][l].status = "IM_AD"
                /\ cache' = [cache EXCEPT
                        ![c][l].need_ack = @ - 1
                    ]

            need_ack_is_zero ==
                cache[c][l].need_ack - 1 = 0

            when_im_a_ack_non_zero ==
                /\ cache[c][l].status = "IM_A"
                /\ ~need_ack_is_zero
                /\ cache' = [cache EXCEPT
                        ![c][l].need_ack = @ - 1
                    ]

            when_im_a_ack_zero ==
                /\ cache[c][l].status = "IM_A"
                /\ need_ack_is_zero
                /\ cache' = [cache EXCEPT
                        ![c][l].status = "M",
                        ![c][l].need_ack = 0
                    ]

            when_sm_a_ack_non_zero ==
                /\ cache[c][l].status = "SM_A"
                /\ ~need_ack_is_zero
                /\ cache' = [cache EXCEPT
                        ![c][l].need_ack = @ - 1
                    ]

            when_sm_a_ack_zero ==
                /\ cache[c][l].status = "SM_A"
                /\ need_ack_is_zero
                /\ cache' = [cache EXCEPT
                        ![c][l].status = "M",
                        ![c][l].need_ack = 0
                    ]
        IN
        /\ msg.type = "Inv-Ack"
        /\ msg.to_cpu = c
        /\ msg.line = l

        /\ cpu_network' = cpu_network \ {msg}
        /\ \/ when_im_ad
           \/ when_im_a_ack_non_zero
           \/ when_im_a_ack_zero
           \/ when_sm_a_ack_non_zero
           \/ when_sm_a_ack_zero

        /\ UNCHANGED cache_to_llc
        /\ UNCHANGED llc_to_cache
        /\ cpu_unchanged


CpuDataToReq(c, l) ==
    \E msg \in cpu_network:
        LET
            when_is_d ==
                /\ cache[c][l].status = "IS_D"
                /\ cache' = [cache EXCEPT
                        ![c][l].status = "S",
                        ![c][l].data = msg.data
                    ]

            when_im_ad ==
                /\ cache[c][l].status = "IM_AD"
                /\ cache' = [cache EXCEPT
                        ![c][l].status = "M",
                        ![c][l].data = msg.data
                    ]
        IN
        /\ msg.type = "DataToReq"
        /\ msg.to_cpu = c
        /\ msg.line = l

        /\ cpu_network' = cpu_network \ {msg}
        /\ \/ when_is_d
           \/ when_im_ad

        /\ UNCHANGED cache_to_llc
        /\ UNCHANGED llc_to_cache
        /\ cpu_unchanged


CpuReplacement(c, l) ==
    LET
        new_req == [
            type |-> "PutS",
            line |-> l
        ]

        when_s ==
            /\ cache[c][l].status = "S"
            /\ cache' = [cache EXCEPT
                    ![c][l].status = "SI_A"
                ]
            /\ cache_to_llc' = [cache_to_llc EXCEPT ![c] = Append(@, new_req)]

        putm_req == [
            type |-> "PutM",
            line |-> l,
            data |-> cache[c][l].data
        ]

        when_m ==
            /\ cache[c][l].status = "M"
            /\ cache' = [cache EXCEPT
                    ![c][l].status = "MI_A"
                ]
            /\ cache_to_llc' = [cache_to_llc EXCEPT ![c] = Append(@, putm_req)]
    IN
    /\ ~stopped
    /\ \/ when_s
       \/ when_m

    /\ cpu_unchanged
    /\ UNCHANGED llc_to_cache
    /\ UNCHANGED cpu_network


CpuPutAck(c, l) ==
    LET
        resp == llc_to_cache[c][1]

        when_si_a ==
            /\ cache[c][l].status = "SI_A"
            /\ cache' = [cache EXCEPT
                    ![c][l].status = "I",
                    ![c][l].data = nil
                ]

        when_mi_a ==
            /\ cache[c][l].status = "MI_A"
            /\ cache' = [cache EXCEPT
                    ![c][l].status = "I",
                    ![c][l].data = nil
                ]

        when_ii ==
            /\ cache[c][l].status = "II"
            /\ cache' = [cache EXCEPT
                    ![c][l].status = "I",
                    ![c][l].data = nil
                ]
    IN
    /\ llc_to_cache[c] # <<>>
    /\ resp.type = "Put-Ack"
    /\ resp.line = l

    /\ llc_to_cache' = [llc_to_cache EXCEPT ![c] = Tail(@)]
    /\ \/ when_si_a
       \/ when_mi_a
       \/ when_ii

    /\ UNCHANGED cache_to_llc
    /\ UNCHANGED cpu_network
    /\ cpu_unchanged


----------------------------------------------------------

llc_unchanged ==
    /\ UNCHANGED cache
    /\ UNCHANGED mem
    /\ UNCHANGED cpu_network
    /\ UNCHANGED global_data
    /\ UNCHANGED stopped


get_from_mem(l, old) ==
    IF old = nil
        THEN mem[l]
        ELSE old

LLCGetS(c, l) ==
    LET
        req == cache_to_llc[c][1]

        data_resp == [
            type |-> "DataResp",
            line |-> l,
            data |-> llc'[l].data,
            ack |-> 0
        ]

        when_invalid ==
            /\ llc[l].status = "I"
            /\ llc' = [llc EXCEPT
                    ![l].status = "S",
                    ![l].data = get_from_mem(l, @),
                    ![l].sharer = @ \union {c}
                ]
            /\ llc_to_cache' = [llc_to_cache EXCEPT ![c] = Append(@, data_resp)]
        
        when_shared ==
            /\ llc[l].status = "S"
            /\ llc' = [llc EXCEPT
                    ![l].sharer = @ \union {c}
                ]
            /\ llc_to_cache' = [llc_to_cache EXCEPT ![c] = Append(@, data_resp)]
        
        owner == llc[l].owner

        fwd_gets_resp == [
            type |-> "Fwd-GetS",
            req_cpu |-> c,
            line |-> l
        ]
        
        when_mutable ==
            /\ llc[l].status = "M"
            /\ llc' = [llc EXCEPT
                    ![l].status = "S_D",
                    ![l].sharer = {owner, c}
                ]
            /\ llc_to_cache' = [llc_to_cache EXCEPT
                    ![owner] = Append(@, fwd_gets_resp)
                ]
    IN
    /\ cache_to_llc[c] # <<>>
    /\ req.line = l
    /\ req.type = "GetS"

    /\ cache_to_llc' = [cache_to_llc EXCEPT ![c] = Tail(@)]
    /\ \/ when_invalid
       \/ when_shared
       \/ when_mutable

    /\ llc_unchanged


LLCGetM(c, l) ==
    LET
        req == cache_to_llc[c][1]

        data_resp == [
            type |-> "DataResp",
            line |-> l,
            data |-> llc'[l].data,
            ack |-> 0
        ]

        handle_when_invalid ==
            /\ llc[l].status = "I"
            /\ llc' = [llc EXCEPT
                    ![l].status = "M",
                    ![l].data = get_from_mem(l, @),
                    ![l].owner = c
                ]
            /\ llc_to_cache' = [llc_to_cache EXCEPT ![c] = Append(@, data_resp)]
        
        data_resp_ack == [
            type |-> "DataResp",
            line |-> l,
            data |-> llc'[l].data,
            ack |-> Cardinality(llc[l].sharer \ {c})
        ]

        inv_resp == [
            type |-> "Inv",
            req_cpu |-> c,
            line |-> l
        ]

        push_to_cache_network ==
            llc_to_cache' = [recv \in CPU |->
                LET old == llc_to_cache[recv] IN
                    IF recv = c THEN
                        Append(old, data_resp_ack)
                    ELSE IF recv \in llc[l].sharer THEN
                        Append(old, inv_resp)
                    ELSE
                        old
            ]

        update_when_nil(old) ==
            IF old = nil THEN mem[l] ELSE old

        handle_when_shared ==
            /\ llc[l].status = "S"
            /\ llc' = [llc EXCEPT
                    ![l].status = "M",
                    ![l].data = update_when_nil(@),
                    ![l].owner = c,
                    ![l].sharer = {}
                ]
            /\ push_to_cache_network


        fwd_getm_resp == [
            type |-> "Fwd-GetM",
            req_cpu |-> c,
            line |-> l
        ]

        owner == llc[l].owner

        handle_when_mutable ==
            /\ llc[l].status = "M"
            /\ llc' = [llc EXCEPT ![l].owner = c]
            /\ llc_to_cache' = [llc_to_cache EXCEPT
                    ![owner] = Append(@, fwd_getm_resp)]
    IN
    /\ cache_to_llc[c] # <<>>
    /\ req.line = l
    /\ req.type = "GetM"

    /\ cache_to_llc' = [cache_to_llc EXCEPT ![c] = Tail(@)]
    /\ \/ handle_when_invalid
       \/ handle_when_shared
       \/ handle_when_mutable

    /\ llc_unchanged


LLCDataM(c, l) ==
    LET
        req == cache_to_llc[c][1]

        when_s_d ==
            /\ llc[l].status = "S_D"
            /\ llc' = [llc EXCEPT
                    ![l].status = "S",
                    ![l].data = req.data,
                    ![l].owner = nil
                ]
    IN
    /\ cache_to_llc[c] # <<>>
    /\ req.line = l
    /\ req.type = "DataM"

    /\ cache_to_llc' = [cache_to_llc EXCEPT ![c] = Tail(@)]
    /\ when_s_d

    /\ UNCHANGED llc_to_cache
    /\ llc_unchanged


LLCPutS(c, l) ==
    LET
        req == cache_to_llc[c][1]

        new_resp == [
            type |-> "Put-Ack",
            line |-> l
        ]

        when_s_last ==
            /\ llc[l].status = "S"
            /\ llc[l].sharer = {c}
            /\ llc' = [llc EXCEPT
                    ![l].status = "I",
                    ![l].sharer = {}
                ]
            /\ llc_to_cache' = [llc_to_cache EXCEPT ![c] = Append(@, new_resp)]

        when_s_not_last ==
            /\ llc[l].status = "S"
            /\ llc[l].sharer # {c}
            /\ llc' = [llc EXCEPT
                    ![l].sharer = @ \ {c}
                ]
            /\ llc_to_cache' = [llc_to_cache EXCEPT ![c] = Append(@, new_resp)]

        when_m ==
            /\ llc[l].status = "M"
            /\ UNCHANGED llc
            /\ llc_to_cache' = [llc_to_cache EXCEPT ![c] = Append(@, new_resp)]
    IN
    /\ cache_to_llc[c] # <<>>
    /\ req.line = l
    /\ req.type = "PutS"

    /\ cache_to_llc' = [cache_to_llc EXCEPT ![c] = Tail(@)]
    /\ \/ when_s_last
       \/ when_s_not_last
       \/ when_m

    /\ llc_unchanged


LLCPutM(c, l) ==
    LET
        req == cache_to_llc[c][1]

        put_ack_resp == [
            type |-> "Put-Ack",
            line |-> l
        ]

        send_put_ack ==
            /\ llc_to_cache' = [llc_to_cache
                    EXCEPT ![c] = Append(@, put_ack_resp)]

        when_m_owner ==
            /\ llc[l].status = "M"
            /\ llc[l].owner = c
            /\ llc' = [llc EXCEPT
                    ![l].status = "I",
                    ![l].data = req.data,
                    ![l].owner = nil
                ]
            /\ send_put_ack

        when_m_non_owner ==
            /\ llc[l].status = "M"
            /\ llc[l].owner # c
            /\ UNCHANGED llc
            /\ send_put_ack

        when_sd ==
            /\ llc[l].status = "S_D"
            /\ llc' = [llc EXCEPT
                    ![l].sharer = @ \ {c}
                ]
            /\ send_put_ack
    IN
    /\ cache_to_llc[c] # <<>>
    /\ req.line = l
    /\ req.type = "PutM"

    /\ cache_to_llc' = [cache_to_llc EXCEPT ![c] = Tail(@)]
    /\ \/ when_m_owner
       \/ when_m_non_owner
       \/ when_sd

    /\ llc_unchanged

----------------------------------------------------------

StopCpuAction ==
    /\ ~stopped
    /\ stopped' = TRUE
    /\ UNCHANGED cache
    /\ UNCHANGED llc
    /\ UNCHANGED <<cache_to_llc, llc_to_cache, cpu_network>>
    /\ UNCHANGED mem
    /\ UNCHANGED global_data

----------------------------------------------------------

StopCond ==
    /\ \A c \in CPU:
        /\ cache_to_llc[c] = <<>>
        /\ llc_to_cache[c] = <<>>
    /\ cpu_network = {}

TerminateCond ==
    /\ StopCond
    /\ stopped

Terminated ==
    /\ TerminateCond
    /\ UNCHANGED vars


Next ==
    \/ \E c \in CPU, l \in Line:
        \/ CpuLoad(c, l)
        \/ CpuDataDir(c, l)

        \/ CpuRequestStore(c, l)
        \/ CpuUpdate(c, l)

        \/ CpuFwdGetS(c, l)
        \/ CpuFwdGetM(c, l)
        \/ CpuInv(c, l)

        \/ CpuInvAck(c, l)
        \/ CpuDataToReq(c, l)

        \/ CpuReplacement(c, l)
        \/ CpuPutAck(c, l)

        \/ LLCGetS(c, l)
        \/ LLCGetM(c, l)
        \/ LLCDataM(c, l)
        \/ LLCPutS(c, l)
        \/ LLCPutM(c, l)
    \/ StopCpuAction
    \/ Terminated


Spec == Init /\ [][Next]_vars

FairSpec == Spec /\ WF_vars(Next)

----------------------------------------------------------

AlwaysTerminate == <> TerminateCond

StopCondNoActiveStatus ==
    LET
        cond ==
            \A c \in CPU, l \in Line:
                cache[c][l].status \in CacheStatus
    IN
        StopCond => cond


CacheCoherenceInv ==
    \A l \in Line:
        LET
            shared_list == {c \in CPU: cache[c][l].status = "S"}

            mutable_list == {c \in CPU: cache[c][l].status = "M"}

            cond ==
                /\ mutable_list # {} => shared_list = {}
                /\ Cardinality(mutable_list) <= 1
        IN
            cond


LLCMStateOwnerNonNull ==
    \A l \in Line:
        llc[l].status = "M" => llc[l].owner # nil


CacheStableStateInv ==
    \A c \in CPU, l \in Line:
        cache[c][l].status \in CacheStatus =>
            /\ cache[c][l].need_ack = 0


CacheStateMInv ==
    \A c \in CPU, l \in Line:
        cache[c][l].status = "M" =>
            /\ cache[c][l].data # nil

CacheStateSInv ==
    \A c \in CPU, l \in Line:
        cache[c][l].status = "S" =>
            /\ cache[c][l].data # nil

CacheStateIInv ==
    \A c \in CPU, l \in Line:
        cache[c][l].status = "I" =>
            /\ cache[c][l].data = nil


ReadWriteStatusInv ==
    LET
        all_status == CacheStatus \union CacheTransientStatus
    IN
    /\ ReadableStatus \subseteq all_status
    /\ WritableStatus \subseteq all_status
    /\ WritableStatus \subseteq ReadableStatus


CacheCoherenceInvV2 ==
    \A l \in Line:
        LET
            shared_list == {c \in CPU: cache[c][l].status \in ReadableStatus}

            mutable_list == {c \in CPU: cache[c][l].status \in WritableStatus}

            cond ==
                /\ mutable_list # {} => shared_list = mutable_list
                /\ Cardinality(mutable_list) <= 1
        IN
            cond


LLCWhenMutableInv ==
    \A l \in Line:
        llc[l].status = "M" =>
            /\ llc[l].owner # nil
            /\ llc[l].sharer = {}


LLCWhenSharedInv ==
    \A l \in Line:
        llc[l].status = "S" =>
            /\ llc[l].owner = nil
            /\ llc[l].sharer # {}


LLCWhenInvalidInv ==
    \A l \in Line:
        llc[l].status = "I" =>
            /\ llc[l].owner = nil
            /\ llc[l].sharer = {}


GlobalDataCoherence ==
    \A c \in CPU, l \in Line:
        cache[c][l].status \in ReadableStatus =>
            /\ cache[c][l].data = global_data[l]


NotPossibleCpuStates ==
    \A c \in CPU, l \in Line:
        LET
            resp == llc_to_cache[c][1]

            llc_msg_existed(type) ==
                /\ llc_to_cache[c] # <<>>
                /\ resp.type = type
                /\ resp.line = l

            inv_resp == llc_msg_existed("Inv")
            fwd_gets_resp == llc_msg_existed("Fwd-GetS")
            fwd_getm_resp == llc_msg_existed("Fwd-GetM")
            data_from_dir == llc_msg_existed("DataResp")

            cpu_net_existed(type) ==
                \E msg \in cpu_network:
                    /\ msg.type = type
                    /\ msg.to_cpu = c
                    /\ msg.line = l

            data_from_owner == cpu_net_existed("DataToReq")
            inv_ack_msg == cpu_net_existed("Inv-Ack")

            when_i ==
                /\ cache[c][l].status = "I"
                /\ \/ fwd_gets_resp
                   \/ fwd_getm_resp

            when_is_d ==
                /\ cache[c][l].status = "IS_D"
                /\ \/ fwd_gets_resp
                   \/ fwd_getm_resp
                   \/ inv_ack_msg

            when_sm_a ==
                /\ cache[c][l].status = "SM_A"
                /\ \/ inv_resp
                   \/ data_from_owner
                   \/ data_from_dir

            when_sm_ad ==
                /\ cache[c][l].status = "SM_AD"
                /\ \/ data_from_owner

            when_s ==
                /\ cache[c][l].status = "S"
                /\ \/ fwd_gets_resp
                   \/ fwd_getm_resp
                   \/ data_from_owner
                   \/ data_from_dir
                   \/ inv_ack_msg

            when_m ==
                /\ cache[c][l].status = "M"
                /\ \/ inv_resp
                   \/ data_from_dir
                   \/ data_from_owner
                   \/ inv_ack_msg

            neg_cond ==
                \/ when_i
                \/ when_is_d
                \/ when_s
                \/ when_sm_a
                \/ when_sm_ad
                \/ when_m
        IN
            ~neg_cond


====

------ MODULE MSI ----
EXTENDS TLC, Integers, Sequences, FiniteSets

CONSTANTS Line, CPU, nil

VARIABLES cache, llc, mem, cache_to_llc, llc_to_cache, cpu_network

vars == <<cache, llc, mem, cache_to_llc, llc_to_cache, cpu_network>>

----------------------------------------------------------

NullCPU == CPU \union {nil}

Value == 20..29

NullValue == Value \union {nil}

CacheStatus == {"I", "S", "M"} \* Stable States

CacheTransientStatus == {"IS_D", "IM_AD", "IM_A"}

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
    type: {"GetS", "GetM"},
    line: Line
]

DataMResp == [
    type: {"DataM"},
    line: Line,
    data: Value
]

CacheToLLC == Seq(GetReq \union DataMResp)


FwdGetType == [
    type: {"Fwd-GetS", "Fwd-GetM"},
    req_cpu: CPU,
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

LLCToCache == Seq(DataRespType \union FwdGetType \union InvType)


CpuNetwork ==
    LET
        InvAckMsg == [type: {"Inv-Ack"}, cpu: CPU, line: Line]

        DataToReqMsg == [type: {"DataToReq"}, cpu: CPU, line: Line, data: Value]
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

----------------------------------------------------------

cpu_unchanged ==
    /\ UNCHANGED <<llc, mem>>

CpuLoad(c, l) ==
    LET
        new_req == [
            type |-> "GetS",
            line |-> l
        ]
    IN
    /\ cache[c][l].status = "I"
    /\ cache' = [cache EXCEPT ![c][l].status = "IS_D"]
    /\ cache_to_llc' = [cache_to_llc EXCEPT
            ![c] = Append(@, new_req)
        ]

    /\ cpu_unchanged
    /\ UNCHANGED llc_to_cache
    /\ UNCHANGED cpu_network


CpuDataDir(c, l) ==
    LET
        new_resp == llc_to_cache[c][1]

        when_is_d ==
            /\ cache[c][l].status = "IS_D"
            /\ cache' = [cache EXCEPT
                    ![c][l].status = "S",
                    ![c][l].data = new_resp.data
                ]
            /\ UNCHANGED cpu_network

        ack_is_zero ==
            \/ new_resp.ack = 0
            \/ cache[c][l].need_ack + new_resp.ack = 0

        when_im_ad_ack_zero ==
            /\ cache[c][l].status = "IM_AD"
            /\ ack_is_zero
            /\ cache' = [cache EXCEPT
                    ![c][l].status = "M",
                    ![c][l].data = new_resp.data,
                    ![c][l].need_ack = 0
                ]
            /\ UNCHANGED cpu_network

        when_im_ad_ack_non_zero ==
            /\ cache[c][l].status = "IM_AD"
            /\ ~ack_is_zero
            /\ cache' = [cache EXCEPT
                    ![c][l].status = "IM_A",
                    ![c][l].data = new_resp.data,
                    ![c][l].need_ack = @ + new_resp.ack
                ]
            /\ UNCHANGED cpu_network
    IN
    /\ llc_to_cache[c] # <<>>
    /\ new_resp.line = l
    /\ new_resp.type = "DataResp"

    /\ llc_to_cache' = [llc_to_cache EXCEPT ![c] = Tail(@)]
    /\ \/ when_is_d
       \/ when_im_ad_ack_zero
       \/ when_im_ad_ack_non_zero

    /\ UNCHANGED cache_to_llc
    /\ cpu_unchanged


CpuRequestStore(c, l) ==
    LET
        new_req == [
            type |-> "GetM",
            line |-> l
        ]
    IN
    /\ cache[c][l].status = "I" \* TODO status = S

    /\ cache' = [cache EXCEPT ![c][l].status = "IM_AD"]
    /\ cache_to_llc' = [cache_to_llc EXCEPT
            ![c] = Append(@, new_req)
        ]

    /\ UNCHANGED llc_to_cache
    /\ UNCHANGED cpu_network
    /\ cpu_unchanged


CpuFwdGetS(c, l) ==
    LET
        new_resp == llc_to_cache[c][1]

        dir_data == [
            type |-> "DataM",
            line |-> l,
            data |-> cache[c][l].data
        ]

        push_to_llc ==
            cache_to_llc' = [cache_to_llc EXCEPT ![c] = Append(@, dir_data)]

        data_to_req_msg == [
            type |-> "DataToReq",
            cpu |-> new_resp.req_cpu,
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
    IN
    /\ llc_to_cache[c] # <<>>
    /\ new_resp.line = l
    /\ new_resp.type = "Fwd-GetS"

    /\ llc_to_cache' = [llc_to_cache EXCEPT ![c] = Tail(@)]
    /\ \/ when_mutable

    /\ cpu_unchanged


CpuFwdGetM(c, l) ==
    LET
        resp == llc_to_cache[c][1]

        data_to_req_msg == [
            type |-> "DataToReq",
            cpu |-> resp.req_cpu,
            line |-> l,
            data |-> cache[c][l].data
        ]

        when_mutable ==
            /\ cache[c][l].status = "M"
            /\ cache' = [cache EXCEPT
                    ![c][l].status = "I"
                ]
            /\ cpu_network' = cpu_network \union {data_to_req_msg}
    IN
    /\ llc_to_cache[c] # <<>>
    /\ resp.line = l
    /\ resp.type = "Fwd-GetM"

    /\ llc_to_cache' = [llc_to_cache EXCEPT ![c] = Tail(@)]
    /\ \/ when_mutable

    /\ UNCHANGED cache_to_llc
    /\ cpu_unchanged


CpuInv(c, l) ==
    LET
        resp == llc_to_cache[c][1]

        inv_ack_msg == [
            type |-> "Inv-Ack",
            cpu |-> resp.req_cpu,
            line |-> l
        ]

        when_shared ==
            /\ cache[c][l].status = "S"
            /\ cache' = [cache EXCEPT
                    ![c][l].status = "I"
                ]
            /\ cpu_network' = cpu_network \union {inv_ack_msg}
    IN
    /\ llc_to_cache[c] # <<>>
    /\ resp.line = l
    /\ resp.type = "Inv"

    /\ llc_to_cache' = [llc_to_cache EXCEPT ![c] = Tail(@)]
    /\ \/ when_shared

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
        IN
        /\ msg.type = "Inv-Ack"
        /\ msg.cpu = c
        /\ msg.line = l

        /\ cpu_network' = cpu_network \ {msg}
        /\ \/ when_im_ad
           \/ when_im_a_ack_non_zero
           \/ when_im_a_ack_zero

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
        /\ msg.cpu = c
        /\ msg.line = l

        /\ cpu_network' = cpu_network \ {msg}
        /\ \/ when_is_d
           \/ when_im_ad

        /\ UNCHANGED cache_to_llc
        /\ UNCHANGED llc_to_cache
        /\ cpu_unchanged

----------------------------------------------------------

llc_unchanged ==
    /\ UNCHANGED cache
    /\ UNCHANGED mem
    /\ UNCHANGED cpu_network

LLCGetS(c, l) ==
    LET
        req == cache_to_llc[c][1]

        data_resp == [
            type |-> "DataResp",
            line |-> l,
            data |-> mem[l],
            ack |-> 0
        ]

        when_invalid ==
            /\ llc[l].status = "I"
            /\ llc' = [llc EXCEPT
                    ![l].status = "S",
                    ![l].data = mem[l],
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
            data |-> mem[l],
            ack |-> 0
        ]

        handle_when_invalid ==
            /\ llc[l].status = "I"
            /\ llc' = [llc EXCEPT
                    ![l].status = "M",
                    ![l].data = mem[l],
                    ![l].owner = c
                ]
            /\ llc_to_cache' = [llc_to_cache EXCEPT ![c] = Append(@, data_resp)]
        
        data_resp_ack == [
            type |-> "DataResp",
            line |-> l,
            data |-> mem[l],
            ack |-> Cardinality(llc[l].sharer)
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

        handle_when_shared ==
            /\ llc[l].status = "S"
            /\ llc' = [llc EXCEPT
                    ![l].status = "M",
                    ![l].data = mem[l],
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
                    ![l].data = req.data
                ]
    IN
    /\ cache_to_llc[c] # <<>>
    /\ req.line = l
    /\ req.type = "DataM"

    /\ cache_to_llc' = [cache_to_llc EXCEPT ![c] = Tail(@)]
    /\ when_s_d

    /\ UNCHANGED llc_to_cache
    /\ llc_unchanged

----------------------------------------------------------

StopCond ==
    /\ \A c \in CPU:
        /\ cache_to_llc[c] = <<>>
        /\ llc_to_cache[c] = <<>>
    /\ cpu_network = {}

TerminateCond ==
    /\ StopCond

Terminated ==
    /\ TerminateCond
    /\ UNCHANGED vars


Next ==
    \/ \E c \in CPU, l \in Line:
        \/ CpuLoad(c, l)
        \/ CpuDataDir(c, l)

        \/ CpuRequestStore(c, l)

        \/ CpuFwdGetS(c, l)
        \/ CpuFwdGetM(c, l)
        \/ CpuInv(c, l)

        \/ CpuInvAck(c, l)
        \/ CpuDataToReq(c, l)

        \/ LLCGetS(c, l)
        \/ LLCGetM(c, l)
        \/ LLCDataM(c, l)
    \/ Terminated


Spec == Init /\ [][Next]_vars

----------------------------------------------------------

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

====

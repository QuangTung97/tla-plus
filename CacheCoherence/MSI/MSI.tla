------ MODULE MSI ----
EXTENDS TLC, Naturals, Sequences, FiniteSets

CONSTANTS Line, CPU, nil

VARIABLES cache, llc, mem, cache_to_llc, llc_to_cache

vars == <<cache, llc, mem, cache_to_llc, llc_to_cache>>

----------------------------------------------------------

NullCPU == CPU \union {nil}

Value == 20..29

NullValue == Value \union {nil}

CacheStatus == {"I", "S", "M"} \* Stable States

CacheActiveStatus == {"None", "IS_D", "IM_AD"}

CacheInfo == [
    status: CacheStatus,
    active_status: CacheActiveStatus,
    data: NullValue
]

LLCActiveStatus == {"None"}

LLCInfo == [
    status: CacheStatus \union {"S_D"},
    active_status: LLCActiveStatus,
    owner: NullCPU,
    sharer: SUBSET CPU,
    data: NullValue
]

CacheToLLC == Seq([
    req: {"GetS", "GetM"},
    line: Line
])

LLCToCache == Seq([
    req: {"DataResp", "Fwd-GetS"},
    line: Line,
    data: NullValue
])

----------------------------------------------------------

TypeOK ==
    /\ cache \in [CPU -> [Line -> CacheInfo]]
    /\ llc \in [Line -> LLCInfo]
    /\ mem \in [Line -> Value]
    /\ cache_to_llc \in [CPU -> CacheToLLC]
    /\ llc_to_cache \in [CPU -> LLCToCache]


init_cache == [
    status |-> "I",
    active_status |-> "None",
    data |-> nil
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

----------------------------------------------------------

CpuLoad(c, l) ==
    LET
        new_req == [
            req |-> "GetS",
            line |-> l
        ]
    IN
    /\ cache[c][l].status = "I"
    /\ cache[c][l].active_status = "None"
    /\ cache' = [cache EXCEPT
            ![c][l].active_status = "IS_D"
        ]
    /\ cache_to_llc' = [cache_to_llc EXCEPT
            ![c] = Append(@, new_req)
        ]

    /\ UNCHANGED <<llc, mem>>
    /\ UNCHANGED llc_to_cache


CpuDataDir(c, l) ==
    LET
        new_resp == llc_to_cache[c][1]

        when_is_d ==
            /\ cache[c][l].active_status = "IS_D"
            /\ cache' = [cache EXCEPT
                    ![c][l].status = "S",
                    ![c][l].active_status = "None",
                    ![c][l].data = new_resp.data
                ]

        when_im_ad ==
            /\ cache[c][l].active_status = "IM_AD"
            /\ cache' = [cache EXCEPT
                    ![c][l].status = "M",
                    ![c][l].active_status = "None",
                    ![c][l].data = new_resp.data
                ]
    IN
    /\ llc_to_cache[c] # <<>>
    /\ new_resp.line = l

    /\ llc_to_cache' = [llc_to_cache EXCEPT ![c] = Tail(@)]
    /\ \/ when_is_d
       \/ when_im_ad

    /\ UNCHANGED cache_to_llc
    /\ UNCHANGED <<llc, mem>>


CpuRequestStore(c, l) ==
    LET
        new_req == [
            req |-> "GetM",
            line |-> l
        ]
    IN
    /\ cache[c][l].status = "I"
    /\ cache[c][l].active_status = "None"

    /\ cache' = [cache EXCEPT
            ![c][l].active_status = "IM_AD"
        ]
    /\ cache_to_llc' = [cache_to_llc EXCEPT
            ![c] = Append(@, new_req)
        ]

    /\ UNCHANGED llc_to_cache
    /\ UNCHANGED <<llc, mem>>

----------------------------------------------------------

llcUnchanged ==
    /\ UNCHANGED cache
    /\ UNCHANGED mem

LLCGetS(c, l) ==
    LET
        req == cache_to_llc[c][1]

        data_resp == [
            req |-> "DataResp",
            line |-> l,
            data |-> mem[l]
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
            req |-> "Fwd-GetS",
            line |-> l,
            data |-> nil
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
    /\ req.req = "GetS"

    /\ cache_to_llc' = [cache_to_llc EXCEPT ![c] = Tail(@)]
    /\ \/ when_invalid
       \/ when_shared
       \/ when_mutable

    /\ llcUnchanged


LLCGetM(c, l) ==
    LET
        req == cache_to_llc[c][1]

        data_resp == [
            req |-> "DataResp",
            line |-> l,
            data |-> mem[l]
        ]

        handle_when_invalid ==
            /\ llc[l].status = "I"
            /\ llc' = [llc EXCEPT
                    ![l].status = "M",
                    ![l].data = mem[l],
                    ![l].owner = c
                ]
            /\ llc_to_cache' = [llc_to_cache EXCEPT ![c] = Append(@, data_resp)]
        
        handle_when_shared ==
            /\ llc[l].status = "S"
            /\ llc' = [llc EXCEPT
                    ![l].status = "M",
                    ![l].data = mem[l],
                    ![l].sharer = {}
                ]
            /\ llc_to_cache' = [llc_to_cache EXCEPT ![c] = Append(@, data_resp)]

        handle_when_mutable ==
            /\ llc[l].status = "M"
            /\ llc' = [llc EXCEPT
                    ![l].status = "M",
                    ![l].data = mem[l]
                ]
            /\ llc_to_cache' = [llc_to_cache EXCEPT ![c] = Append(@, data_resp)]
    IN
    /\ cache_to_llc[c] # <<>>
    /\ req.line = l
    /\ req.req = "GetM"

    /\ cache_to_llc' = [cache_to_llc EXCEPT ![c] = Tail(@)]
    /\ \/ handle_when_invalid
       \/ handle_when_shared
       \/ handle_when_mutable

    /\ llcUnchanged

----------------------------------------------------------

StopCond ==
    /\ \A c \in CPU:
        /\ cache_to_llc[c] = <<>>
        /\ llc_to_cache[c] = <<>>

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

        \/ LLCGetS(c, l)
        \/ LLCGetM(c, l)
    \/ Terminated


Spec == Init /\ [][Next]_vars

----------------------------------------------------------

StopCondNoActiveStatus ==
    LET
        cond ==
            \A c \in CPU, l \in Line:
                cache[c][l].active_status = "None"
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

====

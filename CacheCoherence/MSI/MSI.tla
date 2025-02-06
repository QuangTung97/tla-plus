------ MODULE MSI ----
EXTENDS TLC, Naturals, Sequences

CONSTANTS Line, CPU, nil

VARIABLES cache, llc, mem, cache_to_llc, llc_to_cache

vars == <<cache, llc, mem, cache_to_llc, llc_to_cache>>

----------------------------------------------------------

Value == 20..29

NullValue == Value \union {nil}

CacheStatus == {"I", "S", "M"} \* Stable States

CacheActiveStatus == {"None", "IS_D"}

CacheInfo == [
    status: CacheStatus,
    active_status: CacheActiveStatus,
    data: NullValue
]

LLCActiveStatus == {"None"}

LLCInfo == [
    status: CacheStatus,
    active_status: LLCActiveStatus,
    sharer: SUBSET CPU,
    data: NullValue
]

CacheToLLC == Seq([
    req: {"GetS"},
    line: Line
])

LLCToCache == Seq([
    req: {"DataResp"},
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
    IN
    /\ llc_to_cache[c] # <<>>
    /\ new_resp.line = l

    /\ llc_to_cache' = [llc_to_cache EXCEPT ![c] = Tail(@)]
    /\ cache' = [cache EXCEPT
            ![c][l].status = "S",
            ![c][l].active_status = "None",
            ![c][l].data = new_resp.data
        ]

    /\ UNCHANGED cache_to_llc
    /\ UNCHANGED <<llc, mem>>


----------------------------------------------------------

LLCGetS(c, l) ==
    LET
        req == cache_to_llc[c][1]

        data_resp == [
            req |-> "DataResp",
            line |-> l,
            data |-> mem[l]
        ]
    IN
    /\ cache_to_llc[c] # <<>>
    /\ req.line = l

    /\ cache_to_llc' = [cache_to_llc EXCEPT ![c] = Tail(@)]
    /\ llc' = [llc EXCEPT
            ![l].status = "S",
            ![l].data = mem[l],
            ![l].sharer = @ \union {c}
        ]
    /\ llc_to_cache' = [llc_to_cache EXCEPT
            ![c] = Append(@, data_resp)
        ]
    /\ UNCHANGED cache
    /\ UNCHANGED mem

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
        \/ LLCGetS(c, l)
    \/ Terminated


Spec == Init /\ [][Next]_vars

----------------------------------------------------------

====

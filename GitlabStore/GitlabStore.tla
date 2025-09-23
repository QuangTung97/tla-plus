------ MODULE GitlabStore ----
EXTENDS TLC, Sequences

CONSTANTS Node, Key, LinkKey, nil

VARIABLES
    store, store_ref, ws_links, locked,
    pc, local_key, local_link

vars == <<
    store, store_ref, ws_links, locked,
    pc, local_key, local_link
>>

---------------------------------------------------------------

NullKey == Key \union {nil}
NullLinkKey == LinkKey \union {nil}

PC == {"Init", "CloneProject", "Terminated"}

---------------------------------------------------------------

TypeOK ==
    /\ store \subseteq Key
    /\ store_ref \in [Key -> Seq(LinkKey)]
    /\ locked \subseteq Key
    /\ ws_links \in [LinkKey -> NullKey]

    /\ pc \in [Node -> PC]
    /\ local_key \in [Node -> NullKey]
    /\ local_link \in [Node -> NullLinkKey]

Init ==
    /\ store = {}
    /\ store_ref = [k \in Key |-> <<>>]
    /\ locked = {}
    /\ ws_links = [k \in LinkKey |-> nil]

    /\ pc = [n \in Node |-> "Init"]
    /\ local_key = [n \in Node |-> nil]
    /\ local_link = [n \in Node |-> nil]

---------------------------------------------------------------

lockKey(k) ==
    /\ k \notin locked
    /\ locked' = locked \union {k}

unlockKey(k) ==
    /\ locked' = locked \ {k}

goto(n, label) ==
    pc' = [pc EXCEPT ![n] = label]


setLocal(var, n, val) ==
    var' = [var EXCEPT ![n] = val]

---------------------------

BeginClone(n, k, l) ==
    /\ pc[n] = "Init"
    /\ goto(n, "CloneProject")
    /\ lockKey(k)

    /\ setLocal(local_key, n, k)
    /\ setLocal(local_link, n, l)

    /\ UNCHANGED ws_links
    /\ UNCHANGED store
    /\ UNCHANGED store_ref

---------------------------------------------------------------

TerminateCond ==
    /\ \A n \in Node: pc[n] = "Terminated"

Terminated ==
    /\ TerminateCond
    /\ UNCHANGED vars


Next ==
    \/ \E n \in Node, k \in Key, l \in LinkKey:
        \/ BeginClone(n, k, l)
    \/ Terminated

Spec == Init /\ [][Next]_vars

====

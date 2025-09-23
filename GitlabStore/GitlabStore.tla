------ MODULE GitlabStore ----
EXTENDS TLC

---------------------------------------------------------------

CONSTANTS Node, Key, LinkKey, nil

VARIABLES
    store, store_ref, ws_links, locked,
    pc, local_key, local_link,
    job_pc, job_key, job_link,
    enable_unlink

local_vars == <<
    pc, local_key, local_link
>>

job_vars == <<
    job_pc, job_key, job_link
>>

vars == <<
    store, store_ref, ws_links, locked,
    local_vars,
    job_vars,
    enable_unlink
>>

---------------------------------------------------------------

NullKey == Key \union {nil}
NullLinkKey == LinkKey \union {nil}

PC == {
    "Init",
    "CloneProject", "SetStoreRef",
    "LinkWorkspace",
    "DoDeleteKey",
    "Terminated"
}

---------------------------------------------------------------

TypeOK ==
    /\ store \subseteq Key
    /\ store_ref \in [Key -> (SUBSET LinkKey)]
    /\ locked \subseteq Key
    /\ ws_links \in [LinkKey -> NullKey]

    /\ pc \in [Node -> PC]
    /\ local_key \in [Node -> NullKey]
    /\ local_link \in [Node -> NullLinkKey]

    /\ job_pc \in {"Init", "RemoveStoreRef"}
    /\ job_key \in NullKey
    /\ job_link \in NullLinkKey

    /\ enable_unlink \in BOOLEAN

Init ==
    /\ store = {}
    /\ store_ref = [k \in Key |-> {}]
    /\ locked = {}
    /\ ws_links = [k \in LinkKey |-> nil]

    /\ pc = [n \in Node |-> "Init"]
    /\ local_key = [n \in Node |-> nil]
    /\ local_link = [n \in Node |-> nil]

    /\ job_pc = "Init"
    /\ job_key = nil
    /\ job_link = nil

    /\ enable_unlink = TRUE

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
    LET
        when_reuse ==
            /\ goto(n, "SetStoreRef")

        when_clone ==
            /\ goto(n, "CloneProject")
    IN
    /\ pc[n] = "Init"
    /\ lockKey(k)

    /\ IF k \in store
        THEN when_reuse
        ELSE when_clone

    /\ setLocal(local_key, n, k)
    /\ setLocal(local_link, n, l)

    /\ UNCHANGED ws_links
    /\ UNCHANGED store
    /\ UNCHANGED store_ref
    /\ UNCHANGED job_vars
    /\ UNCHANGED enable_unlink

---------------------------

unchangedLocalVars ==
    /\ UNCHANGED local_key
    /\ UNCHANGED local_link
    /\ UNCHANGED job_vars
    /\ UNCHANGED enable_unlink

CloneProject(n) ==
    LET
        k == local_key[n]
    IN
    /\ pc[n] = "CloneProject"
    /\ goto(n, "SetStoreRef")

    /\ store' = store \union {k} \* TODO clone fail

    /\ unchangedLocalVars
    /\ UNCHANGED locked
    /\ UNCHANGED store_ref
    /\ UNCHANGED ws_links

---------------------------

SetStoreRef(n) ==
    LET
        k == local_key[n]
        l == local_link[n]
    IN
    /\ pc[n] = "SetStoreRef"
    /\ goto(n, "LinkWorkspace")

    /\ store_ref' = [store_ref EXCEPT ![k] = @ \union {l}]

    /\ unchangedLocalVars
    /\ UNCHANGED ws_links
    /\ UNCHANGED store
    /\ UNCHANGED locked

---------------------------

LinkWorkspace(n) ==
    LET
        k == local_key[n]
        l == local_link[n]
    IN
    /\ pc[n] = "LinkWorkspace"
    /\ goto(n, "Terminated")
    /\ unlockKey(k)

    /\ ws_links' = [ws_links EXCEPT ![l] = k]
    /\ setLocal(local_key, n, nil)
    /\ setLocal(local_link, n, nil)

    /\ UNCHANGED job_vars
    /\ UNCHANGED store
    /\ UNCHANGED store_ref
    /\ UNCHANGED enable_unlink

---------------------------------------------------------------

workspaceLinksMatched ==
    \A k \in Key, l \in LinkKey:
        l \in store_ref[k] <=> ws_links[l] = k

jobUnchanged ==
    /\ UNCHANGED store
    /\ UNCHANGED local_vars
    /\ UNCHANGED ws_links
    /\ UNCHANGED enable_unlink

StartFixLink(k, l) ==
    /\ job_pc = "Init"
    /\ lockKey(k)
    /\ l \in store_ref[k]
    /\ ws_links[l] # k

    /\ job_pc' = "RemoveStoreRef"
    /\ job_key' = k
    /\ job_link' = l

    /\ UNCHANGED store_ref
    /\ jobUnchanged

---------------------------

RemoveStoreRef ==
    LET
        k == job_key
        l == job_link
    IN
    /\ job_pc = "RemoveStoreRef"
    /\ job_pc' = "Init"
    /\ unlockKey(k)

    /\ store_ref' = [store_ref EXCEPT ![k] = @ \ {l}]

    /\ job_key' = nil
    /\ job_link' = nil

    /\ jobUnchanged

---------------------------------------------------------------

deleteKeyUnchanged ==
    /\ UNCHANGED job_vars
    /\ UNCHANGED ws_links
    /\ UNCHANGED store_ref
    /\ UNCHANGED local_link
    /\ UNCHANGED enable_unlink

DeleteKey(n, k) ==
    /\ pc[n] = "Init"
    /\ lockKey(k)
    /\ k \in store
    /\ store_ref[k] = {}
    /\ goto(n, "DoDeleteKey")

    /\ setLocal(local_key, n, k)

    /\ UNCHANGED store
    /\ deleteKeyUnchanged

DoDeleteKey(n) ==
    LET
        k == local_key[n]
    IN
    /\ pc[n] = "DoDeleteKey"
    /\ goto(n, "Terminated")
    /\ unlockKey(k)

    /\ store' = store \ {k}
    /\ setLocal(local_key, n, nil)

    /\ deleteKeyUnchanged

---------------------------------------------------------------

Unlink(l) ==
    /\ enable_unlink
    /\ ws_links[l] # nil
    /\ ws_links' = [ws_links EXCEPT ![l] = nil]

    /\ UNCHANGED local_vars
    /\ UNCHANGED job_vars
    /\ UNCHANGED enable_unlink
    /\ UNCHANGED locked
    /\ UNCHANGED <<store, store_ref>>


DisableUnlink ==
    /\ enable_unlink
    /\ enable_unlink' = FALSE

    /\ UNCHANGED local_vars
    /\ UNCHANGED job_vars
    /\ UNCHANGED locked
    /\ UNCHANGED <<store, store_ref, ws_links>>

---------------------------------------------------------------

TerminateCond ==
    /\ \A n \in Node: pc[n] = "Terminated"
    /\ locked = {}
    /\ workspaceLinksMatched
    /\ ~enable_unlink

Terminated ==
    /\ TerminateCond
    /\ UNCHANGED vars


Next ==
    \/ \E n \in Node, k \in Key, l \in LinkKey:
        \/ BeginClone(n, k, l)

    \/ \E n \in Node:
        \/ CloneProject(n)
        \/ SetStoreRef(n)
        \/ LinkWorkspace(n)
        \/ DoDeleteKey(n)

    \/ \E k \in Key, l \in LinkKey:
        \/ StartFixLink(k, l)
    \/ RemoveStoreRef

    \/ \E n \in Node, k \in Key:
        \/ DeleteKey(n, k)

    \/ \E l \in LinkKey:
        \/ Unlink(l)
    \/ DisableUnlink
    \/ Terminated

Spec == Init /\ [][Next]_vars

FairSpec == Spec /\ WF_vars(Next)

---------------------------------------------------------------

AlwaysTerminated == []<> TerminateCond


WorkspaceLinkInv ==
    \A l \in LinkKey:
        LET
            k == ws_links[l]
        IN
            k # nil => l \in store_ref[k]


StoreRefInv ==
    \A k \in Key:
        store_ref[k] # {} => k \in store


TerminatedInv ==
    TerminateCond =>
        \A n \in Node:
            /\ local_key[n] = nil
            /\ local_link[n] = nil

====

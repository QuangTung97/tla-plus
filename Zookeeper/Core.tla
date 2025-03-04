------ MODULE Core ----
EXTENDS TLC, FiniteSets, Sequences, Naturals, Common

CONSTANTS Group, Key, Value, Client, nil

ASSUME IsFiniteSet(Group)

VARIABLES server_log, server_state

vars == <<server_log, server_state>>

---------------------------------------------------------------------------

Zxid == 21..29

NullZxid == Zxid \union {nil}

Xid == 30..39

Session == 11..19

NullSession == Session \union {nil}

LogEntry ==
    LET
        session_entry == [
            type: {"NewSession"},
            zxid: Zxid,
            sess: Session
        ]

        put_entry == [
            type: {"Put"},
            zxid: Zxid,
            group: Group,
            key: Key,
            val: Value
        ]
    IN
        UNION {session_entry, put_entry}

KeySeq == Key

StateInfo == [
    val: Value,
    sess: NullSession \* For Ephemeral ZNodes
]

---------------------------------------------------------------------------

TypeOK ==
    /\ server_log \in Seq(LogEntry)
    /\ DOMAIN server_state = Group
    /\ \A g \in Group: IsMapOf(server_state[g], KeySeq, StateInfo)

Init ==
    /\ server_log = <<>>
    /\ server_state = [g \in Group |-> <<>>]

---------------------------------------------------------------------------

TerminateCond ==
    /\ TRUE

Terminated ==
    /\ TerminateCond
    /\ UNCHANGED vars


Next ==
    \/ Terminated

Spec == Init /\ [][Next]_vars

---------------------------------------------------------------------------

====

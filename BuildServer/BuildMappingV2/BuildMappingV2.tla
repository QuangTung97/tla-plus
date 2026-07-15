---- MODULE BuildMappingV2 ----
EXTENDS TLC, Naturals, FiniteSets

CONSTANT Workspace, Value, nil, max_build_num

VARIABLES
    pc,
    last_build_id, build_id_list, build_state_map,
    current_build_id, last_bazel_pid,
    god_bazel_id, bazel_pid_map, bazel_pid_list

vars == <<
    pc,
    last_build_id, build_id_list, build_state_map,
    current_build_id, last_bazel_pid,
    god_bazel_id, bazel_pid_map, bazel_pid_list
>>

---------------------------------------------------------

Null(S) == S \union {nil}
Extra(S, e) == S \union {e}

max_build_id == 20 + max_build_num
BuildID == 21..max_build_id

BazelPID == 31..(30 + max_build_num)

BuildState == [
    ws: Workspace,
    is_current: BOOLEAN,
    bazel_pid: Null(BazelPID),
    value: Null(Value)
]

BazelState == [
    build_id: Null(BuildID),
    recv: BOOLEAN,
    pending: Null(Value)
]

PC == {"Init", "SetBazelPID"}

---------------------------------------------------------

TypeOK ==
    /\ pc \in [Workspace -> PC]

    /\ last_build_id \in Extra(BuildID, 20)
    /\ build_id_list \subseteq BuildID
    /\ build_state_map \in [BuildID -> Null(BuildState)]

    /\ current_build_id \in [Workspace -> Null(BuildID)]
    /\ god_bazel_id \in [BuildID -> Null(BazelPID)]

    /\ last_bazel_pid \in Extra(BazelPID, 30)
    /\ bazel_pid_map \in [BazelPID -> Null(BazelState)]
    /\ bazel_pid_list \subseteq BazelPID

Init ==
    /\ pc = [w \in Workspace |-> "Init"]

    /\ last_build_id = 20
    /\ build_id_list = {}
    /\ build_state_map = [id \in BuildID |-> nil]

    /\ current_build_id = [w \in Workspace |-> nil]
    /\ god_bazel_id = [id \in BuildID |-> nil]

    /\ last_bazel_pid = 30
    /\ bazel_pid_map = [pid \in BazelPID |-> nil]
    /\ bazel_pid_list = {}

---------------------------------------------------------

goto(w, l) ==
    pc' = [pc EXCEPT ![w] = l]

StartBuild(w) ==
    LET
        id == last_build_id'
        pid == last_bazel_pid'

        old_id == current_build_id[w]
        old_state == build_state_map[old_id]

        state == [
            ws |-> w,
            is_current |-> TRUE,
            bazel_pid |-> nil,
            value |-> nil
        ]

        update_state ==
            [build_state_map EXCEPT ![id] = state]

        clear_old_if_exist ==
            IF old_id # nil THEN
                [update_state EXCEPT
                    ![old_id].is_current = FALSE,
                    ![old_id].bazel_pid = nil
                ]
            ELSE
                update_state

        old_pid == update_state[old_id].bazel_pid

        old_bazel_pid_exist ==
            /\ old_id # nil
            /\ old_pid # nil

        update_bazel_map ==
            IF old_bazel_pid_exist THEN
                [bazel_pid_map EXCEPT ![old_pid] = nil]
            ELSE
                bazel_pid_map
    IN
    /\ pc[w] = "Init"
    /\ last_build_id < max_build_id

    /\ goto(w, "SetBazelPID")
    /\ last_build_id' = last_build_id + 1
    /\ last_bazel_pid' = last_bazel_pid + 1
    /\ god_bazel_id' = [god_bazel_id EXCEPT ![id] = pid]
    /\ build_state_map' = clear_old_if_exist
    /\ build_id_list' = build_id_list \union {id}
    /\ current_build_id' = [current_build_id EXCEPT ![w] = id]
    /\ bazel_pid_map' = update_bazel_map

    /\ UNCHANGED bazel_pid_list

---------------------------------------------------------

SetBazelPID(w) ==
    LET
        id == current_build_id[w]
        pid == god_bazel_id[id]

        old_state == build_state_map[id]

        init_bazel_state == [
            build_id |-> id,
            recv |-> FALSE,
            pending |-> nil
        ]

        old_bazel_state ==
            IF bazel_pid_map[pid] = nil
                THEN init_bazel_state
                ELSE bazel_pid_map[pid]

        new_bazel_state == [old_bazel_state EXCEPT
            !.build_id = id,
            !.pending = nil
        ]

        new_value == old_bazel_state.pending

        new_state == [old_state EXCEPT
            !.bazel_pid = pid,
            !.value = new_value
        ]

        old_pid_list == bazel_pid_list
        new_pid_list ==
            IF old_bazel_state.pending # nil THEN
                old_pid_list \ {pid}
            ELSE
                old_pid_list
    IN
    /\ pc[w] = "SetBazelPID"

    /\ goto(w, "Init")
    /\ build_state_map' = [build_state_map EXCEPT ![id] = new_state]
    /\ bazel_pid_list' = new_pid_list
    /\ bazel_pid_map' = [bazel_pid_map EXCEPT ![pid] = new_bazel_state]

    /\ UNCHANGED current_build_id
    /\ UNCHANGED build_id_list
    /\ UNCHANGED god_bazel_id
    /\ UNCHANGED last_bazel_pid
    /\ UNCHANGED last_build_id

---------------------------------------------------------

SetBuildValue(pid, v) ==
    LET
        old_bazel_state == bazel_pid_map[pid]

        allow_cond ==
            old_bazel_state # nil => old_bazel_state.recv = FALSE

        new_bazel_state ==
            IF old_bazel_state = nil
                THEN [build_id |-> nil, recv |-> TRUE, pending |-> v]
                ELSE [old_bazel_state EXCEPT !.recv = TRUE]

        id == new_bazel_state.build_id
        update_state ==
            IF id # nil THEN
                build_state_map' = [build_state_map EXCEPT ![id].value = v]
            ELSE
                UNCHANGED build_state_map

        new_list == bazel_pid_list \union{pid}
        update_pid_list ==
            IF id # nil THEN
                bazel_pid_list' = new_list \ {pid}
            ELSE
                bazel_pid_list' = new_list
    IN
    /\ allow_cond

    /\ bazel_pid_map' = [bazel_pid_map EXCEPT ![pid] = new_bazel_state]
    /\ update_state
    /\ update_pid_list

    /\ UNCHANGED build_id_list
    /\ UNCHANGED pc
    /\ UNCHANGED current_build_id
    /\ UNCHANGED god_bazel_id
    /\ UNCHANGED last_bazel_pid
    /\ UNCHANGED last_build_id

---------------------------------------------------------

RemoveBuildID(id) ==
    /\ id \in build_id_list
    /\ ~build_state_map[id].is_current

    /\ build_id_list' = build_id_list \ {id}
    /\ build_state_map' = [build_state_map EXCEPT ![id] = nil]

    /\ UNCHANGED bazel_pid_map
    /\ UNCHANGED bazel_pid_list
    /\ UNCHANGED current_build_id
    /\ UNCHANGED pc
    /\ UNCHANGED god_bazel_id
    /\ UNCHANGED last_bazel_pid
    /\ UNCHANGED last_build_id

---------------------------------------------------------

RemoveBazelID(pid) ==
    /\ pid \in bazel_pid_list

    /\ bazel_pid_list' = bazel_pid_list \ {pid}
    /\ bazel_pid_map' = [bazel_pid_map EXCEPT ![pid] = nil]

    /\ UNCHANGED build_id_list
    /\ UNCHANGED current_build_id
    /\ UNCHANGED build_state_map
    /\ UNCHANGED pc
    /\ UNCHANGED god_bazel_id
    /\ UNCHANGED last_bazel_pid
    /\ UNCHANGED last_build_id

---------------------------------------------------------

build_id_is_current(id) ==
    \E w \in Workspace: current_build_id[w] = id

TerminateCond ==
    /\ last_build_id = max_build_id
    /\ \A w \in Workspace:
        LET
            id == current_build_id[w]
            cond ==
                build_state_map[id].value # nil
        IN
        /\ pc[w] = "Init"
        /\ id # nil => cond

Terminated ==
    /\ TerminateCond
    /\ UNCHANGED vars

---------------------------------

Next ==
    \/ \E w \in Workspace:
        \/ StartBuild(w)
        \/ SetBazelPID(w)
    \/ \E pid \in BazelPID, v \in Value:
        \/ SetBuildValue(pid, v)
    \/ \E id \in BuildID: RemoveBuildID(id)
    \/ \E pid \in BazelPID: RemoveBazelID(pid)
    \/ Terminated

Spec == Init /\ [][Next]_vars

---------------------------------------------------------

BuildIDListInv ==
    build_id_list = {id \in BuildID: build_state_map[id] # nil}


is_non_build_pid(pid) ==
    /\ bazel_pid_map[pid] # nil
    /\ bazel_pid_map[pid].build_id = nil

is_building_pid(pid) ==
    /\ bazel_pid_map[pid] # nil
    /\ bazel_pid_map[pid].build_id # nil

exist_state_with_pid(pid) ==
    \E id \in BuildID:
        /\build_state_map[id] # nil
        /\build_state_map[id].bazel_pid = pid

BazelPIDListInv ==
    LET
        non_build_set == {pid \in BazelPID: is_non_build_pid(pid)}
        building_set == {pid \in BazelPID: is_building_pid(pid)}
        state_bazel_set == {pid \in BazelPID: exist_state_with_pid(pid)}
    IN
        /\ bazel_pid_list = non_build_set
        /\ building_set = state_bazel_set


BazelStateInv ==
    \A pid \in BazelPID:
        LET
            state == bazel_pid_map[pid]
            cond == state.build_id = nil <=> state.pending # nil
        IN
            state # nil => cond


CurrentBuildMapInv ==
    LET
        valid_ws == {w \in Workspace: current_build_id[w] # nil}
        current_set == {id \in BuildID: build_id_is_current(id)}
    IN
        Cardinality(valid_ws) = Cardinality(current_set)


BuildStateIsCurrentInv ==
    \A id \in BuildID:
        LET
            left ==
                /\ build_state_map[id] # nil
                /\ build_state_map[id].is_current
        IN
            left <=> build_id_is_current(id)


BuildStateIsNotCurrentInv ==
    \A id \in BuildID:
        LET
            state == build_state_map[id]
            cond == ~state.is_current => state.bazel_pid = nil
        IN
            state # nil => cond

====

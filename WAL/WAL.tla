------ MODULE WAL ----
EXTENDS TLC, Naturals, Sequences

CONSTANTS max_num_value, num_page, nil, max_restart

VARIABLES
    status, mem_wal, disk_wal,
    current, checkpoint, latest_gen,
    current_val, previous_val, prev_non_full,
    mem_values, god_values,
    num_restart

vars == <<
    status, mem_wal, disk_wal,
    current, checkpoint, latest_gen,
    current_val, previous_val, prev_non_full,
    mem_values, god_values,
    num_restart
>>

--------------------------------------------------------------------------

seq_remove(s, i) == SubSeq(s, 1, i - 1) \o SubSeq(s, i + 1, Len(s))
ASSUME seq_remove(<<3, 4, 5, 6>>, 2) = <<3, 5, 6>>
ASSUME seq_remove(<<3, 4>>, 2) = <<3>>
ASSUME seq_remove(<<5, 6>>, 1) = <<6>>

-------------------

put_at_pos(s, pos, v) ==
    LET
        old_len == Len(s)
        new_len == IF pos > old_len THEN pos ELSE old_len
        new_value_fn(x) ==
            IF x = pos THEN
                v
            ELSE IF x <= old_len THEN
                s[x]
            ELSE
                nil
    IN
        [x \in 1..new_len |-> new_value_fn(x)]

ASSUME put_at_pos(<<>>, 2, 3) = <<nil, 3>>
ASSUME put_at_pos(<<5, 6, 7>>, 3, 9) = <<5, 6, 9>>
ASSUME put_at_pos(<<5, 6, 7>>, 5, 9) = <<5, 6, 7, nil, 9>>

-------------------

seq_get_sub(s, i, j) ==
    IF j < i
        THEN <<>>
        ELSE SubSeq(s, i, j)

ASSUME seq_get_sub(<<2, 3, 4>>, 1, 2) = <<2, 3>>
ASSUME seq_get_sub(<<>>, 1, 0) = <<>>
ASSUME seq_get_sub(<<5, 6, 7>>, 1, 1) = <<5>>

--------------------------------------------------------------------------

max_value == 20 + max_num_value

Value == 20..max_value

NullValue == Value \union {nil}

PageIndex == 1..num_page

PageNum == 0..max_value

Generation == 0..(1 + max_restart)

Position == [
    gen: Generation,
    num: PageNum
]

init_position == [
    gen |-> 0,
    num |-> 0
]

Page == [
    pos: Position,
    non_full: BOOLEAN,
    val: NullValue,
    prev: NullValue
]

NullPage == Page \union {nil}

init_page == [
    pos |-> init_position,
    non_full |-> FALSE,
    val |-> nil,
    prev |-> nil
]

--------------------------------------------------------------------------

TypeOK ==
    /\ mem_wal \in Seq(Page)
    /\ disk_wal \in [PageIndex -> Page]
    /\ status \in {"Init", "Ready"}
    /\ current \in Position
    /\ checkpoint \in PageNum
    /\ latest_gen \in Generation
    /\ current_val \in Value
    /\ previous_val \in Seq(Value)
    /\ prev_non_full \in BOOLEAN

    /\ mem_values \in Seq(NullPage)
    /\ god_values \in Seq(NullPage)
    /\ num_restart \in 0..max_restart

Init ==
    /\ mem_wal = <<>>
    /\ disk_wal = [x \in PageIndex |-> init_page]
    /\ status = "Init"
    /\ current = init_position
    /\ current_val = 20
    /\ checkpoint = 0
    /\ latest_gen = 0
    /\ previous_val = <<20>>
    /\ prev_non_full = FALSE

    /\ mem_values = <<>>
    /\ god_values = <<>>
    /\ num_restart = 0

--------------------------------------------------------------------------

pos_to_index(pos) == ((pos - 1) % num_page) + 1

Recover ==
    LET
        page_num == current.num + 1
        index == pos_to_index(page_num)
        page == disk_wal[index]

        when_equal ==
            /\ current' = page.pos
            /\ mem_values' = put_at_pos(mem_values, page_num, page)
            /\ prev_non_full' = page.non_full
            /\ UNCHANGED status
            /\ UNCHANGED latest_gen

        get_last_val ==
            IF mem_values # <<>>
                THEN mem_values[Len(mem_values)].val
                ELSE nil

        when_not_equal ==
            /\ status' = "Ready"
            /\ latest_gen' = latest_gen + 1
            /\ current' = [current EXCEPT !.gen = latest_gen']
            /\ UNCHANGED mem_values
            /\ UNCHANGED prev_non_full

        cond ==
            /\ ~prev_non_full
            /\ page.pos.gen >= current.gen
            /\ page.pos.num = current.num + 1
    IN
    /\ status = "Init"
    /\ IF cond
        THEN when_equal
        ELSE when_not_equal
    /\ UNCHANGED checkpoint
    /\ UNCHANGED mem_wal
    /\ UNCHANGED disk_wal
    /\ UNCHANGED current_val
    /\ UNCHANGED god_values
    /\ UNCHANGED num_restart
    /\ UNCHANGED previous_val


AddToLog(non_full) ==
    LET
        entry == [
            pos |-> current',
            non_full |-> non_full,
            val |-> current_val',
            prev |-> "invalid"
        ]

        append_entry == [entry EXCEPT
            !.prev = previous_val[Len(previous_val)]
        ]

        do_append ==
            \* Plus one to avoid overwrite checkpoint page
            /\ current.num + 1 < checkpoint + num_page
            /\ current' = [current EXCEPT !.num = @ + 1]
            /\ previous_val' = Append(previous_val, current_val')
            /\ mem_wal' = Append(mem_wal, append_entry)

        last == Len(mem_wal)
        last_entry == mem_wal[last]

        update_entry == [entry EXCEPT
            !.prev = previous_val[Len(previous_val) - 1]
        ]

        do_update ==
            /\ UNCHANGED current
            /\ previous_val' = [previous_val EXCEPT
                    ![Len(previous_val)] = current_val']
            /\ IF last > 0 /\ last_entry.pos.num = update_entry.pos.num
                THEN mem_wal' = [mem_wal EXCEPT ![last] = update_entry]
                ELSE mem_wal' = Append(mem_wal, update_entry)
    IN
    /\ status = "Ready"
    /\ current_val < max_value
    /\ current_val' = current_val + 1
    /\ prev_non_full' = non_full
    /\ IF prev_non_full
        THEN do_update
        ELSE do_append

    /\ UNCHANGED status
    /\ UNCHANGED disk_wal
    /\ UNCHANGED <<mem_values, god_values>>
    /\ UNCHANGED num_restart
    /\ UNCHANGED checkpoint
    /\ UNCHANGED latest_gen


doFlushToDisk(i) ==
    LET
        p == mem_wal[i]
        page_num == p.pos.num
        index == pos_to_index(page_num)
    IN
    /\ mem_wal' = seq_remove(mem_wal, i)
    /\ disk_wal' = [disk_wal EXCEPT ![index] = p]

    /\ mem_values' = put_at_pos(mem_values, page_num, p)
    /\ god_values' = put_at_pos(god_values, page_num, p)

FlushToDisk ==
    /\ status = "Ready"
    /\ mem_wal # <<>>
    /\ \E i \in DOMAIN mem_wal: doFlushToDisk(i)

    /\ UNCHANGED status
    /\ UNCHANGED current_val
    /\ UNCHANGED current
    /\ UNCHANGED num_restart
    /\ UNCHANGED checkpoint
    /\ UNCHANGED latest_gen
    /\ UNCHANGED previous_val
    /\ UNCHANGED prev_non_full


flushed_lsn ==
    IF mem_wal = <<>>
        THEN current.num
        ELSE mem_wal[1].pos.num - 1

IncreaseCheckpoint ==
    /\ status = "Ready"
    /\ checkpoint < flushed_lsn
    /\ checkpoint' = checkpoint + 1

    /\ UNCHANGED current
    /\ UNCHANGED current_val
    /\ UNCHANGED prev_non_full
    /\ UNCHANGED <<mem_values, god_values>>
    /\ UNCHANGED status
    /\ UNCHANGED mem_wal
    /\ UNCHANGED disk_wal
    /\ UNCHANGED num_restart
    /\ UNCHANGED latest_gen
    /\ UNCHANGED previous_val


RECURSIVE find_first_non_valid(_)
find_first_non_valid(values) ==
    LET e == values[1] IN
    IF Len(values) = 0 THEN
        1
    ELSE IF e = nil THEN
        1
    ELSE IF e.non_full THEN
        2
    ELSE
        1 + find_first_non_valid(Tail(values))

highest_valid_pos ==
    find_first_non_valid(god_values) - 1

Restart ==
    LET
        cp_index == pos_to_index(checkpoint)

        new_prev_non_full ==
            IF checkpoint > 0
                THEN disk_wal[cp_index].non_full
                ELSE FALSE

        loaded_gen ==
            IF checkpoint > 0
                THEN disk_wal[cp_index].pos.gen
                ELSE 0

        new_current == [
            gen |-> loaded_gen,
            num |-> checkpoint
        ]
    IN
    /\ num_restart < max_restart
    /\ num_restart' = num_restart + 1
    /\ status' = "Init"
    /\ mem_wal' = <<>>
    /\ current' = new_current
    /\ mem_values' = seq_get_sub(mem_values, 1, checkpoint)
    /\ god_values' = seq_get_sub(god_values, 1, highest_valid_pos)
    /\ prev_non_full' = new_prev_non_full
    /\ previous_val' = seq_get_sub(previous_val, 1, highest_valid_pos + 1)

    /\ UNCHANGED current_val
    /\ UNCHANGED disk_wal
    /\ UNCHANGED checkpoint
    /\ UNCHANGED latest_gen

--------------------------------------------------------------------------

TerminateCond ==
    /\ status = "Ready"
    /\ current_val = max_value
    /\ mem_wal = <<>>

Terminated ==
    /\ TerminateCond
    /\ UNCHANGED vars

Next ==
    \/ Recover
    \/ \E non_full \in BOOLEAN: AddToLog(non_full)
    \/ FlushToDisk
    \/ IncreaseCheckpoint
    \/ Restart
    \/ Terminated

Spec == Init /\ [][Next]_vars

FairSpec == Spec /\ WF_vars(Next)

--------------------------------------------------------------------------

AlwaysTerminated == []<> TerminateCond


Consistency ==
    status = "Ready" => mem_values = god_values


LogAlwaysIncrease ==
    \A i, j \in DOMAIN god_values:
        i < j /\ god_values[i] # nil /\ god_values[j] # nil
            => god_values[i].val < god_values[j].val


MemValuesLessThanGodValues ==
    Len(mem_values) <= Len(god_values)


LogPreviousValInv ==
    \A i \in 1..highest_valid_pos:
        i > 1 /\ god_values[i] # nil /\ god_values[i - 1] # nil
            => god_values[i].prev = god_values[i - 1].val


CheckPointInv ==
    checkpoint <= Len(god_values)


TerminateInv ==
    TerminateCond =>
        /\ \A i \in DOMAIN god_values: god_values[i] # nil

====

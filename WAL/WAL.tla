------ MODULE WAL ----
EXTENDS TLC, Naturals, Sequences

CONSTANTS max_num_value, num_page, nil, max_restart

VARIABLES
    status, mem_wal, disk_wal,
    current, checkpoint,
    current_val,
    mem_values, god_values,
    num_restart

vars == <<
    status, mem_wal, disk_wal,
    current, checkpoint,
    current_val,
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

SeqNum == 0..max_value

Position == [
    gen: Generation,
    num: PageNum,
    seq: SeqNum
]

init_position == [
    gen |-> 0,
    num |-> 0,
    seq |-> 0
]

Page == [
    pos: Position,
    prev: SeqNum,
    val: NullValue
]

NullPage == Page \union {nil}

init_page == [
    pos |-> init_position,
    prev |-> 0,
    val |-> nil
]

--------------------------------------------------------------------------

TypeOK ==
    /\ mem_wal \in Seq(Page)
    /\ disk_wal \in [PageIndex -> Page]
    /\ status \in {"Init", "Ready"}
    /\ current \in Position
    /\ checkpoint \in Position
    /\ current_val \in Value

    /\ mem_values \in Seq(NullPage)
    /\ god_values \in Seq(NullPage)
    /\ num_restart \in 0..max_restart

Init ==
    /\ mem_wal = <<>>
    /\ disk_wal = [x \in PageIndex |-> init_page]
    /\ status = "Init"
    /\ current = init_position
    /\ checkpoint = init_position
    /\ current_val = 20

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
            /\ UNCHANGED status
            /\ UNCHANGED checkpoint

        get_last_val ==
            IF mem_values # <<>>
                THEN mem_values[Len(mem_values)].val
                ELSE nil

        when_not_equal ==
            /\ status' = "Ready"
            /\ current' = [current EXCEPT !.gen = @ + 1] \* TODO reset seq
            /\ checkpoint' = current'
            /\ UNCHANGED mem_values

        cond ==
            /\ page.pos.gen = current.gen
            /\ page.pos.num = current.num + 1
            /\ page.prev = current.seq

    IN
    /\ status = "Init"
    /\ IF cond
        THEN when_equal
        ELSE when_not_equal
    /\ UNCHANGED mem_wal
    /\ UNCHANGED disk_wal
    /\ UNCHANGED current_val
    /\ UNCHANGED god_values
    /\ UNCHANGED num_restart


AddToLog ==
    LET
        inc_seq == [current EXCEPT !.seq = @ + 1]

        entry == [
            pos |-> current',
            prev |-> current.seq,
            val |-> current_val'
        ]

        do_append ==
            /\ current.num < checkpoint.num + num_page
            /\ current' = [inc_seq EXCEPT !.num = @ + 1]
            /\ mem_wal' = Append(mem_wal, entry)

        last_entry == god_values[Len(god_values)]
        update_entry == [entry EXCEPT !.prev = last_entry.prev]

        do_update ==
            /\ mem_wal = <<>>
            /\ current.num > 0
            /\ current' = inc_seq
            /\ mem_wal' = Append(mem_wal, update_entry)
    IN
    /\ status = "Ready"
    /\ current_val < max_value
    /\ current_val' = current_val + 1
    /\ \/ do_append
       \/ do_update

    /\ UNCHANGED status
    /\ UNCHANGED disk_wal
    /\ UNCHANGED <<mem_values, god_values>>
    /\ UNCHANGED num_restart
    /\ UNCHANGED checkpoint


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


flushed_lsn ==
    IF mem_wal = <<>>
        THEN current.num
        ELSE mem_wal[1].pos.num - 1

IncreaseCheckpoint ==
    LET
        new_num == checkpoint.num + 1
        index == pos_to_index(new_num)
        new_seq == disk_wal[index].pos.seq
    IN
    /\ status = "Ready"
    /\ checkpoint.num < flushed_lsn
    /\ checkpoint' = [checkpoint EXCEPT !.num = new_num, !.seq = new_seq]

    /\ UNCHANGED current
    /\ UNCHANGED current_val
    /\ UNCHANGED <<mem_values, god_values>>
    /\ UNCHANGED status
    /\ UNCHANGED mem_wal
    /\ UNCHANGED disk_wal
    /\ UNCHANGED num_restart


RECURSIVE find_first_non_valid(_, _)
find_first_non_valid(values, prev_seq) ==
    LET e == values[1] IN
    IF Len(values) = 0 THEN
        1
    ELSE IF e = nil THEN
        1
    ELSE IF e.prev # prev_seq THEN
        1
    ELSE
        1 + find_first_non_valid(Tail(values), e.pos.seq)


Restart ==
    LET
        highest_pos == find_first_non_valid(god_values, 0) - 1
    IN
    /\ num_restart < max_restart
    /\ num_restart' = num_restart + 1
    /\ status' = "Init"
    /\ mem_wal' = <<>>
    /\ current' = checkpoint
    /\ mem_values' = seq_get_sub(mem_values, 1, checkpoint.num)
    /\ god_values' = seq_get_sub(god_values, 1, highest_pos)

    /\ UNCHANGED current_val
    /\ UNCHANGED disk_wal
    /\ UNCHANGED checkpoint

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
    \/ AddToLog
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


LogPrevInv ==
    LET
        last_index == find_first_non_valid(god_values, 0) - 1
    IN
    \A i \in 1..last_index:
        IF i > 1
            THEN god_values[i].prev = god_values[i - 1].pos.seq
            ELSE god_values[i].prev = 0


\* TODO add terminate inv

====

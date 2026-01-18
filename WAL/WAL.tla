------ MODULE WAL ----
EXTENDS TLC, Naturals, Sequences

CONSTANTS max_num_value, num_page, nil

VARIABLES
    status, mem_wal, disk_wal,
    latest_page, current_val,
    mem_values, god_values

vars == <<
    status, mem_wal, disk_wal,
    latest_page, current_val,
    mem_values, god_values
>>

seq_remove(s, i) == SubSeq(s, 1, i - 1) \o SubSeq(s, i + 1, Len(s))
ASSUME seq_remove(<<3, 4, 5, 6>>, 2) = <<3, 5, 6>>
ASSUME seq_remove(<<3, 4>>, 2) = <<3>>
ASSUME seq_remove(<<5, 6>>, 1) = <<6>>

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

--------------------------------------------------------------------------

max_value == 20 + max_num_value

Value == 20..max_value

NullValue == Value \union {nil}

PageIndex == 1..num_page

PageNum == 0..(3 * num_page)

Page == [
    num: PageNum,
    val: NullValue
]

init_page == [
    num |-> 0,
    val |-> nil
]

PC == {"Init", "Terminated"}

--------------------------------------------------------------------------

TypeOK ==
    /\ mem_wal \in Seq(Page)
    /\ disk_wal \in [PageIndex -> Page]
    /\ status \in {"Init", "Ready"}
    /\ latest_page \in PageNum
    /\ current_val \in Value

    /\ mem_values \in Seq(NullValue)
    /\ god_values \in Seq(NullValue)

Init ==
    /\ mem_wal = <<>>
    /\ disk_wal = [x \in PageIndex |-> init_page]
    /\ status = "Init"
    /\ latest_page = 0
    /\ current_val = 20

    /\ mem_values = <<>>
    /\ god_values = <<>>

--------------------------------------------------------------------------

pos_to_index(pos) == ((pos - 1) % num_page) + 1

Recover ==
    LET
        pos == latest_page + 1
        index == pos_to_index(pos)
        page == disk_wal[index]

        when_equal ==
            /\ latest_page' = pos \* TODO

        when_not_equal ==
            /\ status' = "Ready"
            /\ UNCHANGED latest_page
            /\ UNCHANGED mem_values
    IN
    /\ status = "Init"
    /\ IF page.num = pos
        THEN when_equal
        ELSE when_not_equal
    /\ UNCHANGED mem_wal
    /\ UNCHANGED disk_wal
    /\ UNCHANGED current_val
    /\ UNCHANGED god_values


AddToLog ==
    LET
        entry == [
            num |-> latest_page',
            val |-> current_val'
        ]
    IN
    /\ status = "Ready"
    /\ current_val < max_value
    /\ current_val' = current_val + 1
    /\ latest_page' = latest_page + 1

    /\ mem_wal' = Append(mem_wal, entry)

    /\ UNCHANGED status
    /\ UNCHANGED disk_wal
    /\ UNCHANGED <<mem_values, god_values>>


doFlushToDisk(i) ==
    LET
        p == mem_wal[i]
        index == pos_to_index(p.num)
    IN
    /\ mem_wal' = seq_remove(mem_wal, i)
    /\ disk_wal' = [disk_wal EXCEPT ![index] = p]

    /\ mem_values' = put_at_pos(mem_values, p.num, p.val)
    /\ god_values' = put_at_pos(god_values, p.num, p.val)

FlushToDisk ==
    /\ status = "Ready"
    /\ mem_wal # <<>>
    /\ \E i \in DOMAIN mem_wal: doFlushToDisk(i)

    /\ UNCHANGED status
    /\ UNCHANGED current_val
    /\ UNCHANGED latest_page


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
    \/ Terminated

Spec == Init /\ [][Next]_vars

--------------------------------------------------------------------------

Consistency ==
    mem_values = god_values

====

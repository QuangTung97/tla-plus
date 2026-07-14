------ MODULE DeleteHistory ----
EXTENDS TLC, Naturals, Sequences

CONSTANTS SyncJob, nil, max_hist_per_job

VARIABLES db_hists, next_hist_id

vars == <<db_hists, next_hist_id>>

--------------------------------------------------------------

HistID == 20..29

Hist == [
    id: HistID,
    job: SyncJob
]

--------------------------------------------------------------

TypeOK ==
    /\ db_hists \in Seq(Hist)
    /\ next_hist_id \in HistID

Init ==
    /\ db_hists = <<>>
    /\ next_hist_id = 20

--------------------------------------------------------------

TerminateCond ==
    /\ TRUE

Terminated ==
    /\ TerminateCond
    /\ UNCHANGED vars

Next ==
    \/ Terminated


Spec == Init /\ [][Next]_vars

====

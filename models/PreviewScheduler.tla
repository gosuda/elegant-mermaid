---- MODULE PreviewScheduler ----
EXTENDS Naturals

CONSTANT MaxRev

VARIABLES latest, inflight, cancelled, displayed

vars == <<latest, inflight, cancelled, displayed>>

TypeOK ==
  /\ latest \in 0..MaxRev
  /\ inflight \in 0..MaxRev
  /\ cancelled \in BOOLEAN
  /\ displayed \in 0..MaxRev

Init ==
  /\ latest = 0
  /\ inflight = 0
  /\ cancelled = FALSE
  /\ displayed = 0

Edited ==
  /\ latest < MaxRev
  /\ latest' = latest + 1
  /\ IF inflight = 0
       THEN /\ inflight' = latest + 1
            /\ cancelled' = FALSE
       ELSE /\ inflight' = inflight
            /\ cancelled' = TRUE
  /\ UNCHANGED displayed

RenderDone ==
  /\ inflight # 0
  /\ IF cancelled
       THEN /\ inflight' = latest
            /\ cancelled' = FALSE
            /\ UNCHANGED displayed
       ELSE /\ inflight' = 0
            /\ cancelled' = FALSE
            /\ displayed' = inflight
  /\ UNCHANGED latest

RenderAborted ==
  /\ inflight # 0
  /\ cancelled
  /\ inflight' = latest
  /\ cancelled' = FALSE
  /\ UNCHANGED <<latest, displayed>>

Next == Edited \/ RenderDone \/ RenderAborted

Spec == Init /\ [][Next]_vars /\ WF_vars(RenderDone)

DisplayedNotAhead == displayed <= latest
IdleMeansCurrent == (inflight = 0) => (displayed = latest)
InflightIsNewer == (inflight # 0) => (inflight > displayed)
CancelledMeansStale == cancelled <=> (inflight # 0 /\ inflight < latest)

DisplayMonotonic == [][displayed' >= displayed]_vars
EventuallyCurrent == <>[](displayed = latest)
====

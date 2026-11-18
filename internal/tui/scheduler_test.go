package tui

import "testing"

const schedulerMaxRev = 4

func enabledEvents(s Scheduler) []Event {
	var events []Event
	if s.Latest < schedulerMaxRev {
		events = append(events, EventEdited)
	}
	if s.Inflight != 0 {
		events = append(events, EventRenderDone)
		if s.Cancelled {
			events = append(events, EventRenderAborted)
		}
	}
	return events
}

func isTerminal(s Scheduler) bool {
	return s.Latest == schedulerMaxRev && s.Inflight == 0 && !s.Cancelled && s.Displayed == schedulerMaxRev
}

func stepChecked(t *testing.T, s Scheduler, e Event) Scheduler {
	t.Helper()
	if !s.enabled(e) {
		t.Fatalf("event %d unexpectedly disabled at %+v", e, s)
	}
	next, _ := Step(s, e)
	if next.Displayed < s.Displayed {
		t.Fatalf("DisplayMonotonic: %+v -> %+v via event %d", s, next, e)
	}
	return next
}

func TestSchedulerReachable(t *testing.T) {
	seen := map[Scheduler]bool{{}: true}
	queue := []Scheduler{{}}
	sawTerminal := false
	for len(queue) > 0 {
		s := queue[0]
		queue = queue[1:]
		assertSchedulerInvariants(t, s)
		sawTerminal = sawTerminal || isTerminal(s)
		for _, e := range enabledEvents(s) {
			next := stepChecked(t, s, e)
			if !seen[next] {
				seen[next] = true
				queue = append(queue, next)
			}
		}
	}
	if !sawTerminal {
		t.Fatalf("terminal state not reached")
	}
	t.Logf("reachable states = %d", len(seen))
	if len(seen) != 25 {
		t.Fatalf("reachable states = %d; TLA+ contract requires 25", len(seen))
	}
}

func typeOK(s Scheduler) bool {
	return s.Latest <= schedulerMaxRev && s.Inflight <= schedulerMaxRev && s.Displayed <= schedulerMaxRev
}

func displayedNotAhead(s Scheduler) bool { return s.Displayed <= s.Latest }

func idleMeansCurrent(s Scheduler) bool { return s.Inflight != 0 || s.Displayed == s.Latest }

func inflightIsNewer(s Scheduler) bool { return s.Inflight == 0 || s.Inflight > s.Displayed }

func cancelledMeansStale(s Scheduler) bool {
	return s.Cancelled == (s.Inflight != 0 && s.Inflight < s.Latest)
}

var schedulerInvariants = []struct {
	name  string
	holds func(Scheduler) bool
}{
	{"TypeOK", typeOK},
	{"DisplayedNotAhead", displayedNotAhead},
	{"IdleMeansCurrent", idleMeansCurrent},
	{"InflightIsNewer", inflightIsNewer},
	{"CancelledMeansStale", cancelledMeansStale},
}

func assertSchedulerInvariants(t *testing.T, s Scheduler) {
	t.Helper()
	for _, invariant := range schedulerInvariants {
		if !invariant.holds(s) {
			t.Fatalf("%s: %+v", invariant.name, s)
		}
	}
}

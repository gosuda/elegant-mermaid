package tui

import "testing"

func TestSchedulerReachable(t *testing.T) {
	seen := map[Scheduler]bool{{}: true}
	queue := []Scheduler{{}}
	for len(queue) > 0 {
		s := queue[0]
		queue = queue[1:]
		assertSchedulerInvariants(t, s)
		var successors []Scheduler
		if s.Latest < 4 {
			next := s
			next.Edit()
			successors = append(successors, next)
		}
		if s.Inflight != 0 {
			next := s
			next.Done()
			successors = append(successors, next)
		}
		for _, next := range successors {
			if !seen[next] {
				seen[next] = true
				queue = append(queue, next)
			}
		}
	}
	if len(seen) != 25 {
		t.Fatalf("reachable states = %d; TLA+ contract requires 25", len(seen))
	}
}

func assertSchedulerInvariants(t *testing.T, s Scheduler) {
	t.Helper()
	if s.Displayed > s.Latest {
		t.Fatalf("DisplayedNotAhead: %+v", s)
	}
	if s.Inflight == 0 && s.Displayed != s.Latest {
		t.Fatalf("IdleMeansCurrent: %+v", s)
	}
	if s.Inflight != 0 && s.Inflight <= s.Displayed {
		t.Fatalf("InflightIsNewer: %+v", s)
	}
	if s.Cancelled != (s.Inflight != 0 && s.Inflight < s.Latest) {
		t.Fatalf("CancelledMeansStale: %+v", s)
	}
}

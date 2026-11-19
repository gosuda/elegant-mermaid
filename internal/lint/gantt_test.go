package lint

import "testing"

func TestGanttRules(t *testing.T) {
	cases := []struct{ code, bad, good string }{
		{"gantt/duplicate-task-id", "gantt\nA :a, 2024-01-01, 1d\nB :a, 2024-01-02, 1d\n", "gantt\nA :a, 2024-01-01, 1d\nB :b, 2024-01-02, 1d\n"},
		{"gantt/undefined-dependency", "gantt\nA :a, after missing, 1d\n", "gantt\nA :a, 2024-01-01, 1d\nB :b, after a, 1d\n"},
		{"gantt/empty-section", "gantt\nsection Empty\n", "gantt\nsection Full\nA :a, 2024-01-01, 1d\n"},
	}
	for _, c := range cases {
		t.Run(c.code, func(t *testing.T) {
			for i, text := range []string{c.bad, c.good} {
				checkGanttRuleCase(t, c.code, text, i)
			}
		})
	}
}

func checkGanttRuleCase(t *testing.T, code, text string, i int) {
	t.Helper()
	ds := Run(Analyze([]byte(text)), Config{Select: []string{code}}).All()
	n := 0
	for _, d := range ds {
		if d.Code == code {
			n++
			if d.Help == "" {
				t.Fatal("missing help")
			}
		}
	}
	if (n > 0) != (i == 0) {
		t.Fatalf("case %d: %v", i, ds)
	}
}

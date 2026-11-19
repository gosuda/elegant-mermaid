package lint

import "testing"

func TestKanbanConsumerRules(t *testing.T) {
	for _, tc := range []struct {
		code, source string
		want         int
	}{
		{"kanban/duplicate-column", "kanban\n  s[S]\n    a[A]\n  a[Column]\n", 1},
		{"kanban/duplicate-task-id", "kanban\n  s[S]\n    a[A]\n  a[Column]\n", 0},
		{"kanban/duplicate-task-id", "kanban\n  s[S]\n    a[A]\n    a[Again]\n", 1},
		{"kanban/no-columns", "kanban\n", 1},
		{"kanban/no-columns", "kanban\n  s[S]\n", 0},
		{"kanban/empty-column", "kanban\n  s[S]\n", 1},
		{"kanban/empty-column", "kanban\n  s[S]\n    a[A]\n", 0},
		{"kanban/duplicate-column", "kanban\n  s[S]\n  s[S]\n", 1},
		{"kanban/duplicate-column", "kanban\n  s[S]\n  t[T]\n", 0},
		{"kanban/duplicate-task-id", "kanban\n  s[S]\n    s[A]\n", 1},
		{"kanban/duplicate-task-id", "kanban\n  s[S]\n    a[A]\n", 0},
	} {
		checkKanbanConsumerCase(t, tc.code, tc.source, tc.want)
	}
}

func checkKanbanConsumerCase(t *testing.T, code, text string, want int) {
	t.Helper()
	a := Analyze([]byte(text))
	result := Run(a, Config{Select: []string{code}})
	count := 0
	for _, d := range result.Lint {
		if d.Code == code {
			count++
			if d.Message == "" || d.Help == "" || d.Span.Start < 0 || d.Span.End > len(text) {
				t.Fatalf("invalid finding: %+v", d)
			}
		}
	}
	if count != want {
		t.Fatalf("%s on %q: got %d want %d", code, text, count, want)
	}
	for _, d := range result.Syntax {
		if d.Code == code {
			t.Fatalf("lint leaked to check: %+v", d)
		}
	}
}

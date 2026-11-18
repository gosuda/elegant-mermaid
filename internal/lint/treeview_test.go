package lint

import "testing"

func TestTreeviewConsumerRules(t *testing.T) {
	for _, tc := range []struct {
		code, source string
		want         int
	}{
		{"treeview/no-nodes", "treeView-beta\n", 1},
		{"treeview/no-nodes", "treeView-beta\na\n", 0},
		{"treeview/duplicate-sibling", "treeView-beta\na\na/ :::x\n", 1},
		{"treeview/duplicate-sibling", "treeView-beta\na\nb\n", 0},
	} {
		checkTreeviewConsumerCase(t, tc.code, tc.source, tc.want)
	}
}

func checkTreeviewConsumerCase(t *testing.T, code, text string, want int) {
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

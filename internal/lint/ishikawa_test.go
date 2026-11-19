package lint

import "testing"

func TestIshikawaConsumerRules(t *testing.T) {
	for _, tc := range []struct {
		code, source string
		want         int
	}{
		{"ishikawa/no-causes", "ishikawa\nproblem\n", 1},
		{"ishikawa/no-causes", "ishikawa\nproblem\n  category\n", 0},
		{"ishikawa/empty-category", "ishikawa\nproblem\n  category\n", 1},
		{"ishikawa/empty-category", "ishikawa\nproblem\n  category\n    cause\n", 0},
		{"ishikawa/duplicate-sibling", "ishikawa\nproblem\n  category\n    cause\n    cause\n", 1},
		{"ishikawa/duplicate-sibling", "ishikawa\nproblem\n  category\n    cause\n    other\n", 0},
		{"ishikawa/deep-nesting", "ishikawa\nproblem\n  a\n    b\n      c\n        d\n          e\n            f\n", 2},
		{"ishikawa/deep-nesting", "ishikawa\nproblem\n  a\n", 0},
	} {
		checkIshikawaConsumerCase(t, tc.code, tc.source, tc.want)
	}
}

func checkIshikawaConsumerCase(t *testing.T, code, text string, want int) {
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
